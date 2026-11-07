# Topologically ordered draft course

**Generated from `lesson-dag.json` by `check_dag.py --write`.**
The edge semantics are **mathematical prerequisites for the intended proof depth**, not Lean imports or a mandated video schedule. The algorithm chooses the earliest original numeric slot whenever multiple nodes are ready.

- **159 vertices:** 150 outlined topics (including introduction), 9 proposed prerequisite insertions.
- **441 directed edges**; 2 roots and 14 sinks; verified acyclic.
- **10 numerical-order violations** among direct prerequisite edges (including proposed insertion slots).
- **29 original-paper endpoint entries** linked to outlined lectures, not a complete mathematical theorem dependency census.

## Backward edges in the current numerical order

These pairs mean that the current numbering introduces a claimed proof-level prerequisite *after* the topic that needs it. They are concrete reasons to edit the outline, split a lecture, or explicitly weaken an early lecture’s proof scope.

| Required first | Dependent | Interpretation |
| --- | --- | --- |
| `033000` Quadratic-form order and positive operators | `029000` Weyl monotonicity and variational eigenvalue inequalities | Existing lesson order is reversed for this proof-level edge |
| `G-COMPACT-SPECTRAL` Compact self-adjoint spectral theorem and compact angle spectra | `051000` Compact angle spectra and classification | Existing lesson order is reversed for this proof-level edge |
| `098000` Symmetric operator ideals and membership | `069000` Norm dependence of Sylvester bounds | Existing lesson order is reversed for this proof-level edge |
| `099000` Hilbert–Schmidt and trace-class operators | `070000` Hilbert–Schmidt Sylvester group estimates | Existing lesson order is reversed for this proof-level edge |
| `107000` Trial spaces, exact subspaces and residuals | `071000` Sylvester identities for compressed blocks | Existing lesson order is reversed for this proof-level edge |
| `098000` Symmetric operator ideals and membership | `094000` Unbounded Sylvester estimates | Existing lesson order is reversed for this proof-level edge |
| `101000` Ideal estimates for compressions and block sums | `094000` Unbounded Sylvester estimates | Existing lesson order is reversed for this proof-level edge |
| `108000` The complementary-block Sylvester equation | `105000` A full proof-readiness assembly | Existing lesson order is reversed for this proof-level edge |
| `109000` Directed sine as a rectangular modulus | `105000` A full proof-readiness assembly | Existing lesson order is reversed for this proof-level edge |
| `110000` The single-angle sine theorem | `105000` A full proof-readiness assembly | Existing lesson order is reversed for this proof-level edge |

## Proposed missing prerequisite lessons

| Proposed ID | Topic | Suggested slot | Needed for |
| --- | --- | --- | --- |
| `G-BANACH-PRINCIPLES` | Uniform boundedness, open mapping and closed graph principles | `006500` | `068000`, `086000` |
| `G-APPROXIMATION` | Weierstrass/Stone–Weierstrass approximation tools | `032500` | `075000` |
| `G-COMPLEX-ANALYSIS` | Complex contour integration and the holomorphic functional calculus | `066500` | `067000` |
| `G-OPERATOR-TOPOLOGIES` | Strong and weak operator convergence; uniform boundedness in limits | `072500` | `082000`, `G-SEMIGROUP-INTEGRATION`, `095000` |
| `G-MEASURE-REPRESENTATION` | Representation of positive functionals by scalar measures | `075500` | `076000` |
| `G-SEMIGROUP-INTEGRATION` | Strong operator integration and semigroup generator foundations | `091500` | `092000` |
| `G-COMPACT-SPECTRAL` | Compact self-adjoint spectral theorem and compact angle spectra | `095500` | `051000`, `096000` |
| `G-RICCATI` | Invariant graph subspaces and operator Riccati equations | `111500` | `117000` |
| `G-SOBOLEV-FOUNDATIONS` | Weak derivatives, Sobolev spaces and boundary traces | `136500` | `137000` |

## Proof target prerequisite closures

| Target | Direct endpoints | Closure size | Gap nodes in closure |
| --- | --- | ---: | --- |
| `two_subspace_geometry` | `049000`, `050000`, `051000` | 52 | `G-APPROXIMATION`, `G-OPERATOR-TOPOLOGIES`, `G-COMPACT-SPECTRAL` |
| `banach_sylvester` | `068000` | 23 | `G-BANACH-PRINCIPLES` |
| `full_scope_sine` | `110000` | 98 | `G-BANACH-PRINCIPLES`, `G-APPROXIMATION`, `G-OPERATOR-TOPOLOGIES`, `G-MEASURE-REPRESENTATION`, `G-SEMIGROUP-INTEGRATION`, `G-COMPACT-SPECTRAL` |
| `other_angle_families` | `112000`, `116000`, `117000` | 102 | `G-BANACH-PRINCIPLES`, `G-APPROXIMATION`, `G-OPERATOR-TOPOLOGIES`, `G-MEASURE-REPRESENTATION`, `G-SEMIGROUP-INTEGRATION`, `G-COMPACT-SPECTRAL`, `G-RICCATI` |
| `selection_and_generalizations` | `119000`, `120000`, `125000`, `126000`, `127000` | 116 | `G-BANACH-PRINCIPLES`, `G-APPROXIMATION`, `G-OPERATOR-TOPOLOGIES`, `G-MEASURE-REPRESENTATION`, `G-SEMIGROUP-INTEGRATION`, `G-COMPACT-SPECTRAL`, `G-RICCATI` |
| `direct_rotation_corrected` | `130000`, `131000`, `132000`, `134000`, `135000` | 60 | None |
| `beam_and_open_problems` | `137000`, `138000`, `139000`, `140000`, `141000`, `142000`, `143000`, `144000` | 134 | `G-BANACH-PRINCIPLES`, `G-APPROXIMATION`, `G-OPERATOR-TOPOLOGIES`, `G-MEASURE-REPRESENTATION`, `G-SEMIGROUP-INTEGRATION`, `G-COMPACT-SPECTRAL`, `G-RICCATI`, `G-SOBOLEV-FOUNDATIONS` |
| `complete_formalization_practicum` | `149000` | 145 | `G-BANACH-PRINCIPLES`, `G-APPROXIMATION`, `G-OPERATOR-TOPOLOGIES`, `G-MEASURE-REPRESENTATION`, `G-SEMIGROUP-INTEGRATION`, `G-COMPACT-SPECTRAL`, `G-RICCATI`, `G-SOBOLEV-FOUNDATIONS` |

## One valid topological order

The six-digit lecture IDs remain stable references. The schedule below may place a larger ID before a smaller one where the mathematical proof prerequisites require that. Proposed gaps are not yet authored lectures.

| Step | ID | Topic |
| ---: | --- | --- |
| 1 | `000000` | Course introduction |
| 2 | `001000` | Linear maps independent of coordinates |
| 3 | `002000` | Norms, distances, and convergence |
| 4 | `003000` | Cauchy sequences and Banach spaces |
| 5 | `004000` | Bounded linear maps and the operator norm |
| 6 | `005000` | The Banach algebra of bounded operators |
| 7 | `006000` | Linear functionals and dual spaces |
| 8 | `G-BANACH-PRINCIPLES` **(proposed)** | Uniform boundedness, open mapping and closed graph principles |
| 9 | `007000` | Real and complex scalars |
| 10 | `008000` | Resolvents and invertibility |
| 11 | `009000` | Inner products and polarization |
| 12 | `010000` | Hilbert spaces and orthogonal complements |
| 13 | `011000` | The projection theorem |
| 14 | `012000` | Adjoints and the Riesz representation theorem |
| 15 | `013000` | Self-adjoint, normal, and unitary maps |
| 16 | `014000` | Isometries, coisometries, and partial isometries |
| 17 | `015000` | Invariant and reducing subspaces |
| 18 | `016000` | Orthogonal sums and block-operator matrices |
| 19 | `017000` | Analysis and synthesis maps |
| 20 | `018000` | Gram matrices and positive Gram operators |
| 21 | `019000` | Frame operators and Parseval identities |
| 22 | `020000` | Orthogonal coordinate embeddings |
| 23 | `021000` | Compressions and Rayleigh–Ritz matrices |
| 24 | `022000` | Overlaps, alignment, and Gram rigidity |
| 25 | `023000` | Gram operators of rectangular maps |
| 26 | `024000` | Eigenvalues, eigenspaces, and algebraic multiplicity |
| 27 | `025000` | Hermitian and self-adjoint matrices |
| 28 | `026000` | The finite spectral theorem |
| 29 | `027000` | Rayleigh quotients and extrema |
| 30 | `028000` | Courant–Fischer min–max |
| 31 | `030000` | Spectral projections for selected sets |
| 32 | `031000` | Ordered gaps versus distance gaps |
| 33 | `032000` | Coordinate-free finite functional calculus |
| 34 | `G-APPROXIMATION` **(proposed)** | Weierstrass/Stone–Weierstrass approximation tools |
| 35 | `033000` | Quadratic-form order and positive operators |
| 36 | `029000` | Weyl monotonicity and variational eigenvalue inequalities |
| 37 | `034000` | Positive square roots and their uniqueness |
| 38 | `035000` | The operator modulus |A| |
| 39 | `036000` | Singular-value decomposition |
| 40 | `037000` | Polar decomposition |
| 41 | `038000` | Partial isometries and polar uniqueness |
| 42 | `039000` | Matrix exponentials from the power series |
| 43 | `040000` | Skew-adjoint generators and unitary flows |
| 44 | `041000` | Operator trigonometric functions |
| 45 | `042000` | Cross-Gram overlap and principal angles |
| 46 | `043000` | Sines, cosines, and cross projections |
| 47 | `044000` | The cosine–sine decomposition |
| 48 | `045000` | Halmos two-projection decomposition |
| 49 | `046000` | Positive cosine and sine operators |
| 50 | `047000` | Acute pairs and transversality |
| 51 | `048000` | The Sz.-Nagy–Kato intertwiner |
| 52 | `049000` | Canonical direct rotation |
| 53 | `050000` | Nonacute angles and defect matching |
| 54 | `052000` | Min–max principles for singular values |
| 55 | `053000` | Low-rank approximation and Eckart–Young |
| 56 | `054000` | Ky Fan sums and inequalities |
| 57 | `055000` | Majorization and weak majorization |
| 58 | `056000` | Convexity and majorization descent |
| 59 | `057000` | Schatten and Frobenius norms |
| 60 | `058000` | Unitary-invariant norms and symmetric gauges |
| 61 | `059000` | Rectangular invariance and zero padding |
| 62 | `060000` | Pinching and block direct sums |
| 63 | `061000` | Quadratic-form inequalities and singular values |
| 64 | `062000` | From scalar division to AX−XB=C |
| 65 | `063000` | Diagonal matrices and the entrywise solution |
| 66 | `064000` | Kronecker sums and Sylvester invertibility |
| 67 | `065000` | Ordered spectral separation |
| 68 | `066000` | Unitary and semigroup representations |
| 69 | `G-COMPLEX-ANALYSIS` **(proposed)** | Complex contour integration and the holomorphic functional calculus |
| 70 | `067000` | Disjoint spectral sets and Rosenblum theory |
| 71 | `068000` | The Banach-space Sylvester lower-bound theorem |
| 72 | `072000` | Infinite-dimensional Hilbert examples |
| 73 | `G-OPERATOR-TOPOLOGIES` **(proposed)** | Strong and weak operator convergence; uniform boundedness in limits |
| 74 | `073000` | Sigma-algebras and Borel sets |
| 75 | `074000` | Measures, integration and L2 |
| 76 | `075000` | Continuous functional calculus and C-star identities |
| 77 | `G-MEASURE-REPRESENTATION` **(proposed)** | Representation of positive functionals by scalar measures |
| 78 | `076000` | Projection-valued measures |
| 79 | `077000` | Scalar spectral measures and polarization |
| 80 | `078000` | Cyclic decompositions and multiplication models |
| 81 | `079000` | Bounded Borel functional calculus |
| 82 | `080000` | Measurable spectral restrictions |
| 83 | `081000` | Resolvents from spectral integrals |
| 84 | `082000` | Spectral approximation by cutoffs |
| 85 | `083000` | Densely defined operators and their graphs |
| 86 | `084000` | Adjoints of unbounded operators |
| 87 | `085000` | Hellinger–Toeplitz and common-domain discipline |
| 88 | `086000` | Resolvents, coercivity, and spectral location |
| 89 | `087000` | Cayley transforms and graph-level equivalence |
| 90 | `088000` | Unbounded spectral theorem and domain calculus |
| 91 | `089000` | Spectral projections and reducing domains |
| 92 | `090000` | Quadratic forms and ordered half-infinite gaps |
| 93 | `091000` | Yosida approximation and bounded truncations |
| 94 | `G-SEMIGROUP-INTEGRATION` **(proposed)** | Strong operator integration and semigroup generator foundations |
| 95 | `092000` | One-parameter unitary groups and their generators |
| 96 | `093000` | Domain-aware Sylvester identities and cutoffs |
| 97 | `095000` | Compactness and finite-rank approximation |
| 98 | `G-COMPACT-SPECTRAL` **(proposed)** | Compact self-adjoint spectral theorem and compact angle spectra |
| 99 | `051000` | Compact angle spectra and classification |
| 100 | `096000` | Approximation numbers and singular-value sequences |
| 101 | `097000` | Ky Fan dominance in Hilbert space |
| 102 | `098000` | Symmetric operator ideals and membership |
| 103 | `069000` | Norm dependence of Sylvester bounds |
| 104 | `099000` | Hilbert–Schmidt and trace-class operators |
| 105 | `070000` | Hilbert–Schmidt Sylvester group estimates |
| 106 | `100000` | Modulus, polar factors, and ideal invariance |
| 107 | `101000` | Ideal estimates for compressions and block sums |
| 108 | `094000` | Unbounded Sylvester estimates |
| 109 | `102000` | Real Hilbert complexification |
| 110 | `103000` | Real and complex spectra and functional calculus |
| 111 | `104000` | Real versions of unbounded Sylvester bounds |
| 112 | `106000` | What changes and what stays invariant |
| 113 | `107000` | Trial spaces, exact subspaces and residuals |
| 114 | `071000` | Sylvester identities for compressed blocks |
| 115 | `108000` | The complementary-block Sylvester equation |
| 116 | `109000` | Directed sine as a rectangular modulus |
| 117 | `110000` | The single-angle sine theorem |
| 118 | `105000` | A full proof-readiness assembly |
| 119 | `111000` | Graph subspaces and tangent geometry |
| 120 | `G-RICCATI` **(proposed)** | Invariant graph subspaces and operator Riccati equations |
| 121 | `112000` | The single-angle tangent theorem |
| 122 | `113000` | Sharp examples and norm-class comparisons |
| 123 | `114000` | Off-diagonal perturbations and block reflection |
| 124 | `115000` | Doubled angles from symmetry |
| 125 | `116000` | The sine-two-theta theorem |
| 126 | `117000` | The tangent-two-theta theorem |
| 127 | `118000` | Why a small doubled sine proves little alone |
| 128 | `119000` | Spectral selection and repulsion |
| 129 | `120000` | Small-angle certification |
| 130 | `121000` | A comparative theorem decision procedure |
| 131 | `122000` | Direct-sum norm comparison |
| 132 | `123000` | Pinching through an involution |
| 133 | `124000` | Ambient sine from an ambient perturbation |
| 134 | `125000` | Non-isometric frames and unequal dimensions |
| 135 | `126000` | Weak spectral gaps and Hilbert–Schmidt estimates |
| 136 | `127000` | The generalized tangent bound |
| 137 | `128000` | Spectral cutoff and finite-rank source lemmas |
| 138 | `129000` | One complete original-paper proof reconstruction |
| 139 | `130000` | Restricted direct-rotation optimality |
| 140 | `131000` | The squared displacement of orthonormal frames |
| 141 | `132000` | Whole-space squared displacement and Q-norms |
| 142 | `133000` | Unsquared ambient displacement is different |
| 143 | `134000` | The four-dimensional real counterexample |
| 144 | `135000` | Corrected scopes and surviving results |
| 145 | `136000` | Classification and realizations of direct rotations |
| 146 | `G-SOBOLEV-FOUNDATIONS` **(proposed)** | Weak derivatives, Sobolev spaces and boundary traces |
| 147 | `137000` | The free-beam operator and its domain |
| 148 | `138000` | Beam Rayleigh–Ritz calculation |
| 149 | `139000` | Comparing angle and Ky Fan beam estimates |
| 150 | `140000` | From subspace bounds to individual modes |
| 151 | `141000` | How much can a distance-only gap say |
| 152 | `142000` | Three subspaces and higher-order interactions |
| 153 | `143000` | Joint movement of eigenvalues and angles |
| 154 | `144000` | Stability of functions of operators |
| 155 | `145000` | From rotation counterexample to real transport matching |
| 156 | `146000` | Rectangular singular-subspace bounds |
| 157 | `147000` | Population-gap spectral statistics |
| 158 | `148000` | Procrustes and spectral embeddings |
| 159 | `149000` | Proof practicum: reconstruct the 1970 theory |

## Reproducibility and limitations

- Topological sorting checks consistency of **the edges we entered**. It cannot establish that our mathematical prerequisite review found every missing theorem.
- The saved August 17, 2026 Lean dependency snapshot reflects project-local declarations at that snapshot; its compiler edges are not equivalent to mathematical proof prerequisites, and its TauCeti pin may differ from the current checkout.
- `lesson-dag.json` is editable independently of the old Manim registry. Run `python3 visualizations/draft-stages/prerequisites/check_dag.py --write` after changing prerequisites.
- Source-result endpoints and suggested insertion numbers are coverage and planning metadata, not assertion that those Lean files or lesson transcripts already exist.
