# Proposed course: Spectral theory, geometry, and Davis–Kahan perturbation theory

**Status:** alternative, transcript-first course proposal. No changes to the existing lecture series, renderer, or journal paper.  
**Mathematical companion:** `papers/dk_formalization_journal/paper.tex`.  
**Primary scope:** explain the mathematics of Davis and Kahan's 1970 *Rotation of Eigenvectors by a Perturbation. III*, including the 29 selected source-result targets (28 proved and one refuted), definitions, proof mechanisms, numerical examples, and original questions. Follow with the journal paper's related mathematics. This does not assert exhaustive coverage of Davis–Kahan Parts I and II or subsequent literature.  
**History:** separately developed, not in this progression.

## First understand spaces and operators; only then study spectral stability

Assume fluency with basic linear algebra and calculus, but **not** with functional analysis, spectral theory, operator geometry, or formal proof assistants. Before talking about the stability of an eigenspace, teach the space in which it lives, the operators acting on it, what their spectra mean, and how their subspaces are represented.

There are **35 proposed foundation lessons** after introduction `000000`. The first stability problem is at `036000`. These are candidate narratives, not a fixed number of videos. Merge or split lessons when it serves understanding; six-digit IDs in increments of 1,000 leave room for insertion.

The mathematical dependency chain is deliberately explicit:

1. **Linear spaces, norms, and completeness:** linear maps independently of coordinates; norms, Cauchy sequences and limits; why Banach spaces are the setting for continuous operator theory.
2. **Hilbert spaces and their geometry:** real/complex inner products; Cauchy–Schwarz, orthogonality, closed subspaces, orthogonal projections and adjoints; which parts need completeness and which do not.
3. **Isometries, frames, and Gram objects:** norm- and inner-product-preserving maps, orthonormal coordinate embeddings, synthesis and analysis, Gram matrices and Gram operators; the distinction between `V*V` and `VV*`.
4. **Spectrum and spectral calculus:** eigenvalues, spectrum as failure of invertibility for bounded operators, resolvents, self-adjointness, the finite-dimensional spectral theorem, spectral projections, and functions of operators.
5. **Operator anatomy and two-subspace geometry:** positivity, square roots, modulus, singular values, symmetric norms, polar decomposition, compression, principal angles, matrix exponentials, and direct rotation.
6. **Only then perturbation theory:** spectral gaps, residuals, Sylvester equations, four angle theorem families, generalizations, branch selection, optimality/counterexample, Hilbert-space and unbounded versions, numerical demonstration and research questions.

Finite-dimensional examples remain the computational entry point, but Banach/Hilbert spaces are introduced **before** the spectrum, not tacked on after the main theorems. Later Unit X rigorously develops infinite-dimensional spectral measures and unbounded domains. Early treatment must be truthful about those distinctions without front-loading advanced analytic proofs.

## Foundation competency gate before `036000`

By the time the listener reaches the first stability lecture, they should be able to work through and explain:

- **Banach/Hilbert:** a norm induces a distance; completeness means every Cauchy sequence converges *inside* the space; a Banach space is complete and normed, a Hilbert space complete with a norm from an inner product. Every Hilbert space is Banach, but not conversely. Finite-dimensional normed real/complex spaces are complete.
- **Bounded maps and adjoints:** bounded linear maps are continuous; the adjoint uses inner products; understand why the expression `A*` is not automatically available on an arbitrary Banach space as a same-space adjoint. Distinguish the Banach dual from the Hilbert adjoint.
- **Isometries and projections:** a linear isometry preserves lengths (and, over real/complex inner-product spaces, inner products); unitary/orthogonal maps are surjective linear isometries. For an orthonormal coordinate embedding `V`, `V*V=I` on coordinates while `VV*` projects onto its range.
- **Gram matrices/operators:** for vectors `v_i`, `G_ij=⟨v_i,v_j⟩`; using synthesis `S`, `G=S*S` is positive semidefinite and determines squared lengths of linear combinations. `SS*` acts on the ambient space and is a *frame operator*, not the coefficient-space Gram operator. For a general bounded `A`, `A*A` is positive and feeds modulus and singular-value theory.
- **Spectral objects:** a self-adjoint matrix has orthogonal spectral projections and can be reconstructed as their eigenvalue-weighted sum. The spectrum of a bounded operator is defined using invertibility, which is more general than eigenvalues in infinite dimensions.
- **Operator constructions:** `|A|=(A*A)^{1/2}`, with the positive square root; SVD and polar factors; scalar functional calculus and skew-adjoint exponentials produce length-preserving flows.
- **Subspace comparison:** principal angles, canonical planes, directed projection errors, and direct rotation do not depend on arbitrary choices of orthonormal frames.

For every foundation topic, require a worked calculation *and* a short conceptual check. An inventory of terminology is not a substitute for comprehension.

## Staged authoring contract, including the Lean connection

1. **Outline and coverage:** use this file as a proposed dependency graph, not the existing Manim catalog as the ordering authority. The original source and journal manuscript determine mathematical coverage.
2. **Audio-first transcript:** write a fully coherent spoken narrative at `tts-lectures/NNNNNN-topic.md`. It must teach without visuals; do not force the teaching order to fit Manim scene boundaries.
3. **Mathematical edit and listening pass:** confirm definitions, examples, hypotheses, quantifiers, norm choices, and pronunciation; use a realistic listener's points of confusion to determine depth.
4. **Mandatory end-of-lecture Lean correspondence:** every mathematical transcript closes with a **spoken explanation of how its principal mathematical symbols appear in Lean**, accompanied by short, source-verified Lean examples that the viewer can read. **Do not relegate this to an optional bibliography or delete it from the lecture.** Start with a side-by-side symbol/type correspondence, show at least one actual library declaration or checked companion example, explain assumptions and typeclass parameters, and distinguish object/definition/theorem/proof. Some purely conceptual bridge lectures may use an existing checked fact rather than invent a theorem.
5. **Source fidelity:** copy any presented declarations from actual `Mathlib`, `TauCeti`, `ForTauCeti`, or `DavisKahan` source available at the target revision. Check the exact namespace/import, name, statement, field ordering, and hypotheses. Avoid fabricated Lean APIs. A source extract is not a claim that the new draft itself has been compiled; separately compile new code when writing a new `.lean` companion.
6. **TTS/code separation within the same lesson:** narrate *what the Lean code expresses* using natural language; display raw Lean in fenced blocks/cards, **not** by having TTS pronounce punctuation, Unicode syntax, typeclass brackets, or proof scripts. Keep the end-section in the transcript so code and mathematics remain connected. The future renderer should distinguish spoken prose from display-only code.
7. **Storyboard derived from transcript:** annotate the already-effective explanation and build Manim visuals around it. A Lean correspondence is one particularly valuable optional-on-screen segment, but need not interrupt the central exposition.
8. **No promotion by accident:** do not touch `visualizations/lectures/`, its registry, the manuscript, or the production renderer while this alternative is being drafted.

**Lean-bridge source pattern already in this repo:** the older transcripts' end cards and `visualizations/lectures/*/facts.lean` (especially projections, polar decomposition, matrix exponential, Rayleigh–Ritz) should be preserved and improved, not dropped. `visualizations/lectures/LEAN_FACTS.md` documents those connections. The central foundations source `ForTauCeti/Analysis/InnerProductSpace/FiniteFrame.lean` (namespace `TauCeti`) defines `finiteAnalysis`, `finiteSynthesis`, `finiteGramOperator` and proves `finiteGramOperator_isPositive`. `ForTauCeti/Analysis/InnerProductSpace/AlignedBasis.lean` documents `Orthonormal.synthesisMapIsometry`. These are candidate actual code anchors, not assertions that every new lecture's Lean companion already exists.

## Course outline

Each row names a **teaching arc**, not an obligation to create a video of fixed duration. The first four units are the foundational sequence; the remaining units complete the Davis–Kahan companion and related applications.

### Unit I — Normed, Banach, and Hilbert spaces; maps between them

*The learner already knows finite vectors and matrices. Explain the spaces and maps that make the later operator notation meaningful, and distinguish what holds in any normed space from what needs an inner product or completeness.*

| Slot | Spoken-lecture focus | Central development |
| --- | --- | --- |
| `001000` | **Linear maps as mathematical objects** — `001000-linear-maps-as-mathematical-objects.md` | Coordinates are descriptions; a linear map and a matrix representation are not identical objects. |
| `002000` | **Norms, distance and convergence** — `002000-norms-distance-and-convergence.md` | Vector norms, induced metrics, sequences, equivalence of norms in finite dimension, and simple function-space examples. |
| `003000` | **Cauchy sequences and completeness** — `003000-cauchy-sequences-and-completeness.md` | Limit points, incomplete normed spaces, and why completing a space matters for analysis. |
| `004000` | **What is a Banach space?** — `004000-what-is-a-banach-space.md` | Definition and finite/infinite examples; bounded linear operators as the natural continuous maps; distinguish the dual space. |
| `005000` | **Inner products and perpendicularity** — `005000-inner-products-and-perpendicularity.md` | Cauchy–Schwarz, real versus complex conjugation, norm from inner product, orthogonal families. |
| `006000` | **What is a Hilbert space?** — `006000-what-is-a-hilbert-space.md` | Complete inner-product spaces; ℝⁿ/ℂⁿ and square-summable sequences; orthonormal expansions and the closed-subspace projection theorem. |
| `007000` | **Bounded operators and the operator norm** — `007000-bounded-operators-and-the-operator-norm.md` | Continuity ↔ boundedness, Banach spaces of operators and finite-dimensional simplifications. |
| `008000` | **Adjoints and Riesz representation** — `008000-adjoints-and-riesz-representation.md` | Inner-product definition of the Hilbert adjoint, finite transpose/conjugate transpose, contrast with Banach dual maps. |
| `009000` | **Isometries, orthogonal and unitary maps** — `009000-isometries-orthogonal-and-unitary-maps.md` | Length preservation, `V*V=I`, surjective versus nonsurjective isometries, and a preview of partial isometries. |
| `010000` | **Frames, synthesis and analysis** — `010000-frames-synthesis-and-analysis.md` | Turn vectors into a coordinate-to-space map and its adjoint; distinguish orthonormal frames from general spanning families. |
| `011000` | **Gram matrices, Gram operators and frame operators** — `011000-gram-matrices-gram-operators-and-frame-operators.md` | Derive `G=S*S` from pairwise inner products, the coefficient quadratic form, positivity, `SS*` on the ambient space and frame bounds. |

### Unit II — Spectrum, eigenvectors, and functional calculus

*Define spectrum only after we know what sort of operator is involved. Use matrices for explicit calculations and keep the infinite-dimensional definition honest.*

| Slot | Spoken-lecture focus | Central development |
| --- | --- | --- |
| `012000` | **Eigenvectors and invariant directions** — `012000-eigenvectors-and-invariant-directions.md` | Scalar action on a direction, examples with repeated eigenvalues, and invariant eigenspaces. |
| `013000` | **What is a spectrum?** — `013000-what-is-a-spectrum.md` | Invertibility of `A−λI` for a bounded operator on a complex Banach space; finite eigenvalues versus approximate/continuous spectrum previews. |
| `014000` | **Self-adjoint operators in finite dimensions** — `014000-self-adjoint-operators-in-finite-dimensions.md` | Real spectrum, orthogonality, normality, and why the adjoint from Unit I matters. |
| `015000` | **The finite-dimensional spectral theorem** — `015000-the-finite-dimensional-spectral-theorem.md` | Orthonormal eigenbasis, projection decomposition and reconstructing the operator. |
| `016000` | **Multiplicity and spectral subspaces** — `016000-multiplicity-and-spectral-subspaces.md` | Distinct eigenvalues versus basis multiplicity; invariant subspaces as intrinsic objects. |
| `017000` | **Projections as operators** — `017000-projections-as-operators.md` | Idempotent/self-adjoint conditions and projection onto a line or plane; connect back to Hilbert closed-subspace projections. |
| `018000` | **Spectral projections and resolvents** — `018000-spectral-projections-and-resolvents.md` | Spectral selection by projection sums in the matrix case; the resolvent as the inverse of `A−λI` off the spectrum. |
| `019000` | **Functions of a self-adjoint operator** — `019000-functions-of-a-self-adjoint-operator.md` | Polynomial functional calculus, square roots and exponentials via spectral projections; proper scope restrictions. |

### Unit III — Modulus, singular values, and operator blocks

*Revisit Gram products as `A*A`: operator modulus now has an existing conceptual foundation rather than appearing as a formal trick.*

| Slot | Spoken-lecture focus | Central development |
| --- | --- | --- |
| `020000` | **Positive operators and positive square roots** — `020000-positive-operators-and-positive-square-roots.md` | Quadratic forms, `A*A≥0`, spectral construction and uniqueness of the positive square root. |
| `021000` | **Operator modulus** — `021000-operator-modulus.md` | `|A|=(A*A)^(1/2)` and the difference from entrywise absolute value; connect Gram products to magnitude. |
| `022000` | **Singular values and SVD** — `022000-singular-values-and-svd.md` | SVD from modulus, left and right singular directions, and the rectangular matrix picture. |
| `023000` | **Norms built from singular values** — `023000-norms-built-from-singular-values.md` | Operator, Frobenius/Hilbert–Schmidt, Schatten and Ky Fan norms; later operator-ideal subtleties. |
| `024000` | **Polar decomposition** — `024000-polar-decomposition.md` | Construct the isometric/partial-isometric factor of `A=U|A|`; kernels and orientation. |
| `025000` | **Invariant and reducing subspaces** — `025000-invariant-and-reducing-subspaces.md` | Internal and crossing operator blocks; self-adjoint block decomposition. |
| `026000` | **Compression through coordinate isometries** — `026000-compression-through-coordinate-isometries.md` | Derive `V*AV`; what changes with the chosen frame and what is intrinsic to its range. |

### Unit IV — Geometry and motion of two subspaces

*All operators can remain fixed here. The learner should know how to compare subspaces before considering a perturbation.*

| Slot | Spoken-lecture focus | Central development |
| --- | --- | --- |
| `027000` | **The geometry encoded by two projections** — `027000-the-geometry-encoded-by-two-projections.md` | Intersections, orthogonal complements and the projection product. |
| `028000` | **Directed error and projection differences** — `028000-directed-error-and-projection-differences.md` | `(I−Q)P`, `(I−P)Q`, and norms of projection differences. |
| `029000` | **Principal angles from overlapping frames** — `029000-principal-angles-from-overlapping-frames.md` | Singular values of `V*W` are cosines of principal angles; Gram matrix of cross-inner-products. |
| `030000` | **Principal planes and the cosine–sine decomposition** — `030000-principal-planes-and-the-cosine-sine-decomposition.md` | Geometric two-plane decomposition, intersections and defect spaces. |
| `031000` | **Reflections and orthogonal motions** — `031000-reflections-and-orthogonal-motions.md` | Reflection compositions and double angles; distinguish changes of basis from motion of subspaces. |
| `032000` | **Matrix exponentials generate rotations** — `032000-matrix-exponentials-generate-rotations.md` | `exp(tK)` for skew-adjoint `K`; derive orthogonality/unitarity and the planar rotation. |
| `033000` | **Acute direct rotations** — `033000-acute-direct-rotations.md` | Canonical maps from projection geometry, polar factors and principal planes. |
| `034000` | **Nonacute direct rotations and their defects** — `034000-nonacute-direct-rotations-and-their-defects.md` | Right angles, existence conditions, square identities and examples. |
| `035000` | **Classifying pairs of subspaces** — `035000-classifying-pairs-of-subspaces.md` | Section 3 classification, realizations and symmetries. |

### Unit V — Now ask the stability question

*With operators, spectra, projections, angles and rotations already defined, ask what changes under approximation. Introduce algebraic residuals and gaps before the named angle theorems.*

| Slot | Spoken-lecture focus | Central development |
| --- | --- | --- |
| `036000` | **When small perturbations turn an eigenvector** — `036000-when-small-perturbations-turn-an-eigenvector.md` | Now revisit the identical-eigenvalue-list two-by-two swap; interpret exactly which spectral objects changed and which did not. |
| `037000` | **Rayleigh quotients, min-max and Weyl estimates** — `037000-rayleigh-quotients-min-max-and-weyl-estimates.md` | Courant-Fischer, eigenvalue approximation and why eigenvalue movement alone does not control spectral subspaces. |
| `038000` | **Rayleigh-Ritz and trial spectral subspaces** — `038000-rayleigh-ritz-and-trial-spectral-subspaces.md` | Trial vectors and coordinate frames; Rayleigh quotients, Ritz blocks and what approximating an invariant subspace means. |
| `039000` | **Residual error versus operator perturbation** — `039000-residual-error-versus-operator-perturbation.md` | Compare A v minus mu v, the residual block, and the difference between A and its approximation; do not conflate these quantities. |
| `040000` | **What does spectral separation mean?** — `040000-what-does-spectral-separation-mean.md` | Spectral sets, target and complement, ordered/interval gaps versus mere spectral distance; choose hypotheses before dividing by a gap. |
| `041000` | **Why Sylvester equations appear** — `041000-why-sylvester-equations-appear.md` | Go from scalar ax minus xb equals c to A X minus X B equals C; solve entrywise in diagonal bases to see how spectral separation enters. |
| `042000` | **Two Sylvester estimates** — `042000-two-sylvester-estimates.md` | Distinguish the Banach-space bounded-inverse estimate and the self-adjoint ordered-gap theorem with their respective hypotheses. |
| `043000` | **When a spectral gap does not give constant one** — `043000-when-a-spectral-gap-does-not-give-constant-one.md` | Interlaced spectral sets, norm-dependent bounds and a concrete counterexample to an overly strong gap assertion. |

### Unit VI — The four Davis–Kahan angle theorems

*Learn the four theorem families in turn, including their geometry, exact assumptions, finite-dimensional proofs and branch distinctions.*

| Slot | Spoken-lecture focus | Central development |
| --- | --- | --- |
| `044000` | **The rank-one sine estimate** — `044000-the-rank-one-sine-estimate.md` | The residual triangle and the first exact residual-over-gap identity. |
| `045000` | **The sine-theta theorem** — `045000-the-sine-theta-theorem.md` | A full finite-dimensional block proof and the directed sine operator. |
| `046000` | **Graph subspaces and tangent angles** — `046000-graph-subspaces-and-tangent-angles.md` | Why tangent asks for a different relationship than sine. |
| `047000` | **The tangent-theta theorem** — `047000-the-tangent-theta-theorem.md` | Ordered separation, Rayleigh-Ritz structure and proof. |
| `048000` | **Where the doubled angle comes from** — `048000-where-the-doubled-angle-comes-from.md` | Reflection, off-diagonal perturbations and the sine of twice the angle. |
| `049000` | **The sine-two-theta theorem** — `049000-the-sine-two-theta-theorem.md` | Precise spectral alternatives and a reflection-based derivation. |
| `050000` | **The tangent-two-theta theorem** — `050000-the-tangent-two-theta-theorem.md` | Off-diagonal blocks, ordered gaps and a proof of the stronger estimate. |
| `051000` | **Four bounds, different answers** — `051000-four-bounds-different-answers.md` | Compare constants, assumptions, full versus directed angles, sharpness and branch ambiguity. |

### Unit VII — General single-angle estimates

*Section 6 deserves full coverage: symmetric norm lemmas, dimension mismatch and weaker separation are not footnotes.*

| Slot | Spoken-lecture focus | Central development |
| --- | --- | --- |
| `052000` | **Unitary-invariant norm comparisons for direct sums** — `052000-unitary-invariant-norm-comparisons-for-direct-sums.md` | Section 6.1 lemma: why separate block estimates can be combined carefully. |
| `053000` | **Pinching and block-diagonal contraction** — `053000-pinching-and-block-diagonal-contraction.md` | Section 6.2 lemma: reflections remove mixed blocks without raising symmetric norms. |
| `054000` | **The ambient sine estimate** — `054000-the-ambient-sine-estimate.md` | Proposition 6.1 and why the ambient perturbation differs from a directed residual. |
| `055000` | **Non-isometric trial frames and unequal dimensions** — `055000-non-isometric-trial-frames-and-unequal-dimensions.md` | Theorem 6.1: lower frame bounds and the epsilon factor. |
| `056000` | **Weak spectral separation and Hilbert-Schmidt control** — `056000-weak-spectral-separation-and-hilbert-schmidt-control.md` | Theorem 6.2: what changes under mere spectral distance, including finite-rank consequences. |
| `057000` | **The generalized tangent theorem** — `057000-the-generalized-tangent-theorem.md` | Theorem 6.3: Rayleigh-Ritz, unequal dimensions and the full tangent argument. |

### Unit VIII — Selecting the correct spectral branch

*Solve the ambiguity left by doubled-angle inequalities; include both Section 8 theorem families.*

| Slot | Spoken-lecture focus | Central development |
| --- | --- | --- |
| `058000` | **Why a small sine of twice an angle is ambiguous** — `058000-why-a-small-sine-of-twice-an-angle-is-ambiguous.md` | Both near-zero and near-right-angle branches can have small sine-two-theta. |
| `059000` | **Ordered gaps and the selected spectral branch** — `059000-ordered-gaps-and-the-selected-spectral-branch.md` | Theorem 8.1: off-diagonal perturbations, noncrossing, existence and uniqueness. |
| `060000` | **Spectral repulsion and quantitative consequences** — `060000-spectral-repulsion-and-quantitative-consequences.md` | Theorem 8.1 block-form, eigenvalue and symmetric-gauge comparisons. |
| `061000` | **Small-perturbation certification** — `061000-small-perturbation-certification.md` | Theorem 8.2: the norm threshold that places angles below pi over four. |

### Unit IX — Direct-rotation optimality and its limits

*Investigate Section 4 objectives separately, then prove the precise refutation and surviving statements of Proposition 4.4.*

| Slot | Spoken-lecture focus | Central development |
| --- | --- | --- |
| `062000` | **Restricted displacement and principal-angle lower bounds** — `062000-restricted-displacement-and-principal-angle-lower-bounds.md` | Proposition 4.1 and Corollary 4.1: singular values of (I-W)P. |
| `063000` | **How squared angular errors add up** — `063000-how-squared-angular-errors-add-up.md` | Proposition 4.2: orthonormal basis comparisons. |
| `064000` | **Squared full displacement and Q-norms** — `064000-squared-full-displacement-and-q-norms.md` | Proposition 4.3 and the norm family for which its conclusion controls displacement. |
| `065000` | **Why full displacement is a different objective** — `065000-why-full-displacement-is-a-different-objective.md` | Distinguish restricted, squared and unsquared ambient movement. |
| `066000` | **The four-dimensional refutation of Proposition 4.4** — `066000-the-four-dimensional-refutation-of-proposition-4-4.md` | Trace-norm competitor, singular-value lists and the precise invalid comparison. |
| `067000` | **What remains true after the correction** — `067000-what-remains-true-after-the-correction.md` | Real versus complex scope, the earlier phase mechanism and the repaired conclusion. |

### Unit X — Infinite-dimensional and unbounded operators

*Return to the original setting with spectral measures, domains, operator ideals and the full scope of the angle results.*

| Slot | Spoken-lecture focus | Central development |
| --- | --- | --- |
| `068000` | **Continuous spectrum beyond finite matrices** — `068000-continuous-spectrum-beyond-finite-matrices.md` | Revisit complete Hilbert spaces and closed invariant subspaces; analyze non-eigenvalue spectral points through examples rather than redefining completeness. |
| `069000` | **Spectral measures and Borel functional calculus** — `069000-spectral-measures-and-borel-functional-calculus.md` | Projection-valued measures and spectral sets, including half-infinite intervals. |
| `070000` | **Unbounded self-adjoint operators and domains** — `070000-unbounded-self-adjoint-operators-and-domains.md` | Hellinger-Toeplitz, common domains and bounded residual extensions. |
| `071000` | **Spectral cutoffs, approximation numbers and finite-rank leakage** — `071000-spectral-cutoffs-approximation-numbers-and-finite-rank-leakage.md` | Section 5.1 and 6.3 lemmas; limits of compressed singular-value data. |
| `072000` | **Symmetric operator ideals and membership conditions** — `072000-symmetric-operator-ideals-and-membership-conditions.md` | Finite ideal norms, Ky Fan dominance and why membership cannot be assumed. |
| `073000` | **Sylvester estimates for unbounded operators** — `073000-sylvester-estimates-for-unbounded-operators.md` | Ordered half-infinite gaps, domain-aware AX-XB and spectral cutoff passage. |
| `074000` | **The full Hilbert-space angle theorems** — `074000-the-full-hilbert-space-angle-theorems.md` | Revisit the four families and the generalized statements with their complete hypotheses. |
| `075000` | **Infinite-dimensional direct-rotation geometry** — `075000-infinite-dimensional-direct-rotation-geometry.md` | Defect dimensions, continuous angle spectrum and nonacute existence criteria. |

### Unit XI — The 1970 paper’s worked numerical example

*Reconstruct the beam/Rayleigh-Ritz calculation of Section 9, not just its headline bounds.*

| Slot | Spoken-lecture focus | Central development |
| --- | --- | --- |
| `076000` | **The free-beam eigenproblem** — `076000-the-free-beam-eigenproblem.md` | Fourth-derivative operator, boundary conditions and the low-dimensional trial space. |
| `077000` | **Sine bounds, double-angle bounds and Ky Fan sums** — `077000-sine-bounds-double-angle-bounds-and-ky-fan-sums.md` | Work through the opening numerical estimates and their different interpretations. |
| `078000` | **Improving the estimates with Rayleigh-Ritz and tangent bounds** — `078000-improving-the-estimates-with-rayleigh-ritz-and-tangent-bounds.md` | Residual reduction, Weinberger comparison and the limitation of unbounded residuals. |
| `079000` | **From subspace error to individual beam modes** — `079000-from-subspace-error-to-individual-beam-modes.md` | Schur complements, internal eigenvector errors and the use of branch selection. |

### Unit XII — Questions left by the 1970 analysis

*Take all four Section 10 questions seriously, distinguishing their 1970 formulation from later research.*

| Slot | Spoken-lecture focus | Central development |
| --- | --- | --- |
| `080000` | **How much does arbitrary spectral separation suffice** — `080000-how-much-does-arbitrary-spectral-separation-suffice.md` | Source Question 10.1: optimal bounds under a pure distance gap. |
| `081000` | **Can we control three-way subspace interactions** — `081000-can-we-control-three-way-subspace-interactions.md` | Source Question 10.2: block geometry beyond pairs of subspaces. |
| `082000` | **Can spectral and angular motion be bounded jointly** — `082000-can-spectral-and-angular-motion-be-bounded-jointly.md` | Source Question 10.3: eigenvalue change alongside rotation. |
| `083000` | **How stable is a function of an operator** — `083000-how-stable-is-a-function-of-an-operator.md` | Source Question 10.4: f(A+H)-f(A), with spectral projections as an illustrative case. |

### Unit XIII — Companion-paper mathematics and applications

*Develop the matching/transport result and modern applications only after the Davis–Kahan core has been taught.*

| Slot | Spoken-lecture focus | Central development |
| --- | --- | --- |
| `084000` | **From the Proposition 4.4 failure to transport optimization** — `084000-from-the-proposition-4-4-failure-to-transport-optimization.md` | Why minimizing real trace-norm displacement leads to coupled principal planes. |
| `085000` | **Real trace-norm transport as weighted matching** — `085000-real-trace-norm-transport-as-weighted-matching.md` | The included follow-on theorem: singleton and pair costs, the global reduction, and proof mechanism. |
| `086000` | **Rectangular perturbations and modern statistical variants** — `086000-rectangular-perturbations-and-modern-statistical-variants.md` | Wedin and Yu-Wang-Samworth; how their assumptions compare with the original angle theory. |
| `087000` | **Spectral embeddings and the motivating DKPS application** — `087000-spectral-embeddings-and-the-motivating-dkps-application.md` | A bounded application path through alignment, Gram matrices and representation error. |

## Coverage crosswalk for the 29 selected 1970 results

Source-result IDs are taken from `dev/davis-kahan-1970-formalization-result-inventory.json`; hypotheses and conclusions are reviewed against `papers/dk_formalization_journal/appendix_result_summaries.tex`. Slots below are proposed teaching locations, not claims that lectures or proofs have been created.

| Original source result ID | Proposed lecture slot(s) |
| --- | --- |
| `S2-sin-theta` | `045000, 074000` |
| `S2-tan-theta` | `047000, 057000, 074000` |
| `S2-sin-two-theta` | `049000, 074000` |
| `S2-tan-two-theta` | `050000, 074000` |
| `DK-3.1-prop` | `033000` |
| `DK-3.2-prop` | `034000` |
| `DK-3.3-prop` | `034000` |
| `DK-3.4-prop` | `034000` |
| `DK-3.1-thm` | `035000` |
| `DK-3.1-cor` | `035000, 075000` |
| `DK-3.5-prop` | `035000` |
| `DK-3.2-cor` | `035000` |
| `DK-4.1-prop` | `062000` |
| `DK-4.1-cor` | `062000` |
| `DK-4.2-prop` | `063000` |
| `DK-4.3-prop` | `064000` |
| `DK-4.4-prop` | `065000–067000` |
| `DK-5.1-thm` | `042000` |
| `DK-5.2-thm` | `042000, 073000` |
| `DK-5.1-lem` | `071000` |
| `DK-6.1-lem` | `052000` |
| `DK-6.2-lem` | `053000` |
| `DK-6.1-prop` | `054000` |
| `DK-6.1-thm` | `055000` |
| `DK-6.2-thm` | `056000` |
| `DK-6.3-thm` | `057000` |
| `DK-6.3-lem` | `071000` |
| `DK-8.1-thm` | `059000–060000` |
| `DK-8.2-thm` | `061000` |

### Non-theorem source material that remains in scope

| Original source material | Main teaching location |
| --- | --- |
| Section 1: Hilbert-space decompositions, source/exact blocks, angular operators, residuals, symmetric norms | Foundations I–IV; transition V; full operator treatment X |
| Section 2: four angle bounds, constants, equality cases and hypotheses | VI, then X |
| Section 3: direct rotation, defects, realization/classification and angle spectrum | IV, then X |
| Section 4: restricted and ambient displacement, Proposition 4.4 and counterexample | IX |
| Section 5: Sylvester estimates, spectral positioning and cutoffs | V and X |
| Section 6: unequal frames, lower frame bounds, symmetric norms and weak gaps | VII and X |
| Section 7: reflections and double-angle proofs | VI and X |
| Section 8: branch choice, repulsion and smallness conditions | VIII |
| Section 9: free beam, estimates (9.1)–(9.11) and Ritz/Weinberger comparisons | XI |
| Section 10: four original questions | XII |
| Journal paper's matching theorem and related applications | XIII |

## Explicit prerequisite relationships

- **Norms → Banach completeness → bounded operators.** Explain the setting in which inverses and limits are studied, then why the bounded-operator spectrum has an analytic definition. Use the complex Banach setting for the general spectrum, with real matrices handled through complexification when needed.
- **Inner products → Hilbert spaces → projections/adjoints → isometries.** An arbitrary Banach space does not supply the same Hilbert adjoint or orthogonal projection theorem. Introduce the dual distinction rather than collapsing these categories.
- **Analysis/synthesis → Gram `S*S` → positive operators → modulus and singular values.** If `S` maps coefficient space into the ambient Hilbert space, its Gram operator lives on coefficient space; `SS*` is the frame operator on ambient space. Use `V*V=I` and `VV*=P` for orthonormal frames, then overlap `V*W` for principal angles.
- **Eigenspaces → spectral theorem → spectral projections → functional calculus.** The Hilbert closed-subspace projection construction precedes the spectral one; a spectral projection adds operator dependence and spectral selection.
- **Isometries/adjoints → skew-adjoint generator → exponential flow → direct rotation.** First derive the continuous isometry and planar example, then introduce the canonical subspace rotation.
- **Compressed operators and residuals → spectral gaps → Sylvester equations → angle theorems.** The first actual stability problem is `036000`.
- **Finite geometry → Hilbert spectral measures/ideals/unbounded domains.** Preview genuine distinctions at the outset; revisit with full proofs in Unit X.
- **Direct rotations + norm objectives → Proposition 4.4 counterexample → matching theorem.** Keep corrected optimality in the original source course and matching in the follow-on unit.

## Lean correspondence crosswalk for early lectures

These are verified file/declaration *anchors* in the supplied repository snapshot, not newly written Lean proofs. For each lecture, inspect the current dependency pin before copying a declaration. The source location should be shown in the end card beside the actual mathematical statement and its Lean counterpart.

| Foundations topic | Mathematical symbol/idea | Source-verified Lean anchor |
| --- | --- | --- |
| Banach and Hilbert structure | continuous `A : E → E`, completeness, inner product | `NormedAddCommGroup`, `CompleteSpace`, `InnerProductSpace`; usage in `visualizations/lectures/002749_rayleigh_ritz/facts.lean` |
| Bounded maps and isometries | `A : E → F`; `‖Vx‖=‖x‖` | `E →L[ℝ] F`, `Isometry X` in the Rayleigh–Ritz companion; `E ≃ₗᵢ[ℝ] E` explained in `visualizations/lectures/LEAN_FACTS.md` |
| Frames and Gram operators | synthesis `S`, analysis `S*`, `G=S*S` | `TauCeti.finiteSynthesis`, `finiteAnalysis`, `finiteGramOperator`, `finiteGramOperator_eq_selfCompAdjoint`, `finiteGramOperator_isPositive` in `ForTauCeti/Analysis/InnerProductSpace/FiniteFrame.lean` (this module defines the Gram product via *analysis* orientation) |
| Orthonormal coordinate embeddings | `V*V=I`, `VV*=P` | `Orthonormal.synthesisMapIsometry` referenced in `ForTauCeti/Analysis/InnerProductSpace/AlignedBasis.lean` |
| Projections and orthogonal splits | `P_K+P_{K⊥}=I` | `K.starProjection_add_starProjection_orthogonal` in `visualizations/lectures/001000_projections/facts.lean` |
| Compression | `V*AV` | `ContinuousLinearMap.compression_def` in `visualizations/lectures/002749_rayleigh_ritz/facts.lean` |
| Modulus and polar decomposition | `|A|`, `A=U|A|` | `LinearMap.polarFactor_comp_operatorAbs` in `visualizations/lectures/002833_polar/facts.lean` |
| Matrix exponential | `exp(tK)` for skew-adjoint `K` | `ContinuousLinearMap.exp_add_smul`, `NormedSpace.exp_mem_unitary_of_mem_skewAdjoint` in `visualizations/lectures/002500_matrix_exponential/facts.lean` |
| Later angle theory | residual predicate, spectral-gap condition | `IsTrialResidual` and `FormBoundedSylvesterGap`, described in `papers/dk_formalization_journal/paper.tex` and used in `DavisKahan/` source modules |

**Lean lesson design:** (1) present the mathematical identity, (2) give its code type, (3) identify each implicit assumption such as `CompleteSpace`, `FiniteDimensional`, `Isometry`, or a spectral-gap predicate, (4) show the actual sourced example/declaration, (5) narrate *why* the coded equality represents the mathematical one. Do not dump the proof development, falsely claim a code excerpt is independently compilable, or replace explanation with a declaration name. Existing `facts.lean` examples are reusable reference patterns.

## Course-scale editorial decisions

- Keep the 29-result crosswalk as the original paper coverage check; new foundations are teaching dependencies, not additional source-results.
- Audio-first mathematical teaching and the **mandatory final Lean bridge** are compatible: explain the mathematics orally; let exact Lean source appear as a synchronized reading card. A listener should still understand the lecture without seeing the code.
- Use concrete Gram examples early: nonorthogonal vectors with `G≠I`, an orthonormal frame with `V*V=I`, and a nonsurjective isometry with `VV*≠I`. These prevent several later confusions about principal angles, compressions and residuals.
- Avoid presenting arbitrary Banach operators as if they had orthogonal spectral projections or Hilbert adjoints. Be explicit about bounded vs unbounded and finite vs infinite dimensions.
- The first serious spectral instability example belongs at `036000`, not the introduction. History is separate. Keep source attribution to mathematical results where relevant.
- Draft lecture IDs are not stable public URLs; renumber these candidate rows while the staged branch is new, without modifying production lecture IDs.

## Source anchors

- `papers/dk_formalization_journal/paper.tex` and `FORMALIZATION_PAPER_SCOPE.md`: companion scope and intended theorem families.
- `papers/dk_formalization_journal/appendix_result_summaries.tex`: source-result statements and hypotheses.
- `prose/distilled_literature/DavisKahan1970_part_III.tex`: section-level source reconstruction, including Section 9 and Section 10.
- `dev/davis-kahan-1970-formalization-result-inventory.json`: 29-result ledger.
- `visualizations/lectures/`: materials available for adaptation, not the ordering authority.
- `papers/optimal_spectral_transport/`: related transport mathematics; do not expand the main course to reproduce this whole program.

**First transcript:** `tts-lectures/000000-course-introduction.md` introduces normed/Banach/Hilbert spaces, isometries, Gram geometry, operators and spectra, and closes with a source-grounded spoken Lean bridge. It intentionally postpones the eigenvector-instability calculation and explicit residual-over-gap argument until the learner reaches the stability unit.

