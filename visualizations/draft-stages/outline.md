# Proposed course: the mathematical foundations of Davis–Kahan theory

**Status:** alternative draft curriculum, not a replacement of the existing Manim lectures, renderer, journal manuscript or Lean modules. **Companion:** `papers/dk_formalization_journal/paper.tex`. **Learner:** familiar with basic finite-dimensional linear algebra and calculus; no prior functional analysis, measure theory, operator ideals, or Lean assumed.

## Purpose and completion standard

This is **not** a syllabus selected from the first Manim scenes. It is a backward design from the **full mathematical proof obligations** in the original Davis–Kahan theory and in the maintained formalization, including substantial mathematics now housed in, or adapted to, TauCeti. The original journal manuscript gives the companion mathematical claims; the original Davis–Kahan source, selected source-result inventory, mathematical prerequisite trace, and upstream-contribution records define the broader teaching coverage. The historical branch remains separate.

**Graduation standard:** a student can reconstruct the important Davis–Kahan proofs from basic linear algebra and calculus by supplying the intermediate analytic lemmas, not simply reciting four theorem statements or reading off Lean's finalized proof. In particular, the student can derive the spectral-subspace angle representations, establish the required Sylvester bound for the actual gap regime, transport the estimate through the appropriate operator ideal, handle unbounded domains, and state exactly where real-to-complex transfer is used. They can also explain the direct-rotation extremal results and the refuted original proposition.

This is a mathematical 'from first principles' standard **relative to the stated starting knowledge**. The course should prove or reconstruct its major functional-analytic tools (spectral theorem routes, projection-valued measures, polar decomposition, majorization, operator ideals and domain-aware estimates), while treating the deepest general-purpose background results as explicitly identified dependencies and proving the versions needed here whenever pedagogically feasible. It does not attempt to rebuild axiomatic set theory or the whole of Mathlib.

**Key difference from the previous draft:** the 29-result ledger is an *endpoint coverage* check, **not** an inventory of everything a student must learn. The foundational curriculum is designed around the manuscript's mathematical prerequisite taxonomy, the source-level proof chain, and the DKPS-to-TauCeti provenance map. This explicitly includes Sylvester equations, PVM/Borel calculus, approximation numbers, majorization, operator ideals, real/complex transfer, and closed/unbounded self-adjoint theory.

## Transcript-first drafting contract

1. `outline.md` is the provisional dependency and coverage map; it may be reordered or split. Its titles are **candidate teaching arcs**, not obligations to make as many short videos as rows. Preserve the six-digit IDs in increments of 1,000, leaving space for inserted lessons. Do not renumber any established lecture in the production tree.
2. `tts-lectures/NNNNNN-topic.md` is the **primary spoken mathematical explanation**. It must teach without Manim; diagrams and animation should be built after the narrative succeeds on its own. A mathematical lesson should have motivation, calculations, formal statements, nontrivial argument, diagnostic examples, and a reconstruction exercise.
3. For **substantive mathematical lessons**, retain a final **mathematics-to-Lean bridge**. It should place actual symbols against actual Lean types, hypotheses and statements and explain what the code proves. Use short, verified declarations from current Mathlib/TauCeti/ForTauCeti/DavisKahan sources; do not invent identifiers or quietly assume upstream modules still exist locally. Display code as display-only, while TTS narrates its meaning, not punctuation. The older `visualizations/lectures/*/facts.lean` files are useful exemplars, not the authority for the syllabus.
4. **The introduction (`000000`) is exempt from the Lean-bridge requirement.** It is orientation, not a detailed mathematics lesson. Other purely transitional/overview lectures may omit it when no mathematical construction is being taught in depth. Do not force a theorem excerpt into an orientation merely to satisfy a template.
5. A transcript's source map records, separately, (i) mathematical source/result, (ii) retained local donor or wrapper, (iii) accepted upstream declaration if actually checked at the chosen TauCeti pin, and (iv) original or adapted provenance where relevant. The topic is retained even if the source that first proved it locally was deleted after upstreaming. No assumptions about donor authorship follow merely from shared roadmap labels.
6. Before promoting a mathematical lecture, check hypotheses, domains, angles and branches, norm membership and scalar field, a worked example, proof reconstruction, source fidelity, and TTS listening quality. A student's ability to reconstruct the proof is the core assessment; compilation and source links support it, rather than replacing it.
7. The staged branch must not overwrite `visualizations/lectures/`, its registry, `ForTauCeti/`, `DavisKahan/`, the journal manuscript, or renderer code.

## Curriculum order and mathematical dependency

The order below is deliberately **foundations first**. The first explicit spectral **stability** question appears only after the major finite- and infinite-dimensional proof ingredients are developed. Some earlier lessons derive algebraic or analytic inequalities that *will later be used* for stability; those are first presented for their own mathematics, not as premature perturbation lectures.

- Linear/normed/Banach spaces → Hilbert geometry, adjoints, projections → frames and Gram operators.
- Self-adjoint spectral theory → positivity and functional calculus → modulus, polar factors, exponentials → two-subspace geometry and direct rotations.
- Min–max, singular values, Ky Fan sums and majorization → symmetric gauge norms → Sylvester operator equations and their gap-sensitive inverses.
- Measure theory/PVM/Borel calculus → unbounded domains, resolvents, spectral cutoff and one-parameter groups → compact operators/ideals and real/complex transfer.
- Only then residual geometry → four angle families → generalized/branch results → extremal rotation/correction → original example/questions → follow-on applications.

### Unit I — Normed spaces, Banach spaces, and bounded maps

*Build the analytic language of operators rather than treating an operator as a matrix with infinitely many rows.*

**Proof checkpoint:** Explain the connection between completeness, boundedness, invertibility, and the resolvent; derive finite examples and at least one infinite-dimensional counterexample.

| ID | Candidate TTS lecture | Mathematical target |
| --- | --- | --- |
| `001000` | **Linear maps independent of coordinates** (`001000-linear-maps-independent-of-coordinates.md`) | Basis changes, composition and why matrix entries are not invariant |
| `002000` | **Norms, distances, and convergence** (`002000-norms-distances-and-convergence.md`) | Norm axioms, induced metrics, equivalent finite-dimensional norms |
| `003000` | **Cauchy sequences and Banach spaces** (`003000-cauchy-sequences-and-banach-spaces.md`) | Incomplete normed-space example; completeness and limits of series |
| `004000` | **Bounded linear maps and the operator norm** (`004000-bounded-linear-maps-and-the-operator-norm.md`) | Continuity equivalence and norm estimates for compositions |
| `005000` | **The Banach algebra of bounded operators** (`005000-the-banach-algebra-of-bounded-operators.md`) | Identity, products, inverse operators and Neumann series |
| `006000` | **Linear functionals and dual spaces** (`006000-linear-functionals-and-dual-spaces.md`) | Dual pairing, dual norms, Hahn–Banach statement and uses |
| `007000` | **Real and complex scalars** (`007000-real-and-complex-scalars.md`) | Why the complex field matters for the spectrum; complexification preview |
| `008000` | **Resolvents and invertibility** (`008000-resolvents-and-invertibility.md`) | The resolvent identity, open resolvent set, and the analytic definition of spectrum |

### Unit II — Hilbert spaces, orthogonality, and subspace geometry

*Add inner products, completeness, projections, adjoints, and the distinction between invariant and reducing subspaces.*

**Proof checkpoint:** Prove the orthogonal projection characterization and derive identities for self-adjoint projections and block decompositions.

| ID | Candidate TTS lecture | Mathematical target |
| --- | --- | --- |
| `009000` | **Inner products and polarization** (`009000-inner-products-and-polarization.md`) | Cauchy–Schwarz, the real/complex conventions and the parallelogram law |
| `010000` | **Hilbert spaces and orthogonal complements** (`010000-hilbert-spaces-and-orthogonal-complements.md`) | Complete inner-product spaces, closed spans, orthonormal families |
| `011000` | **The projection theorem** (`011000-the-projection-theorem.md`) | Nearest-point argument, existence and uniqueness, Pythagoras |
| `012000` | **Adjoints and the Riesz representation theorem** (`012000-adjoints-and-the-riesz-representation-theorem.md`) | How inner products convert bounded functionals to vectors; adjoint identities |
| `013000` | **Self-adjoint, normal, and unitary maps** (`013000-self-adjoint-normal-and-unitary-maps.md`) | Algebraic distinctions, examples, and why commutation matters |
| `014000` | **Isometries, coisometries, and partial isometries** (`014000-isometries-coisometries-and-partial-isometries.md`) | Initial/final spaces; surjective versus non-surjective isometries |
| `015000` | **Invariant and reducing subspaces** (`015000-invariant-and-reducing-subspaces.md`) | Why self-adjoint invariance implies reducing; complement conditions |
| `016000` | **Orthogonal sums and block-operator matrices** (`016000-orthogonal-sums-and-block-operator-matrices.md`) | Derive diagonal/off-diagonal components and their adjoints |

### Unit III — Frames, Gram objects, and coordinate-free geometry

*Connect the notation in the formalization to familiar Gram matrices and move fluently between coordinate and ambient spaces.*

**Proof checkpoint:** For a synthesis map S, derive G=S* S, show positivity and explain why S S* is a different operator; prove projection identities for orthonormal frames.

| ID | Candidate TTS lecture | Mathematical target |
| --- | --- | --- |
| `017000` | **Analysis and synthesis maps** (`017000-analysis-and-synthesis-maps.md`) | How a family of vectors becomes a map from and to coefficient space |
| `018000` | **Gram matrices and positive Gram operators** (`018000-gram-matrices-and-positive-gram-operators.md`) | G=S* S; rank, positivity, and quadratic forms |
| `019000` | **Frame operators and Parseval identities** (`019000-frame-operators-and-parseval-identities.md`) | S S*; tight frames and the orthonormal case |
| `020000` | **Orthogonal coordinate embeddings** (`020000-orthogonal-coordinate-embeddings.md`) | V* V=I, V V*=P and the meaning of the two domains |
| `021000` | **Compressions and Rayleigh–Ritz matrices** (`021000-compressions-and-rayleigh-ritz-matrices.md`) | V* A V, compressed forms, and what compression does not preserve |
| `022000` | **Overlaps, alignment, and Gram rigidity** (`022000-overlaps-alignment-and-gram-rigidity.md`) | Two frames, cross-Gram matrices, unitary changes of coordinates |
| `023000` | **Gram operators of rectangular maps** (`023000-gram-operators-of-rectangular-maps.md`) | A* A versus A A*, nonzero spectral correspondence |

### Unit IV — Finite spectral theory and variational foundations

*Teach what spectra and spectral subspaces are before considering their change.*

**Proof checkpoint:** Prove the finite self-adjoint spectral theorem and Courant–Fischer; explain when a spectral projection is more intrinsic than chosen eigenvectors.

| ID | Candidate TTS lecture | Mathematical target |
| --- | --- | --- |
| `024000` | **Eigenvalues, eigenspaces, and algebraic multiplicity** (`024000-eigenvalues-eigenspaces-and-algebraic-multiplicity.md`) | Diagonal examples, Jordan contrast and invariant subspaces |
| `025000` | **Hermitian and self-adjoint matrices** (`025000-hermitian-and-self-adjoint-matrices.md`) | Real eigenvalues, orthogonal eigenvectors, spectral order |
| `026000` | **The finite spectral theorem** (`026000-the-finite-spectral-theorem.md`) | Spectral decomposition via orthogonal projections, reconstruction |
| `027000` | **Rayleigh quotients and extrema** (`027000-rayleigh-quotients-and-extrema.md`) | Quadratic-form calculation and stationary eigenvectors |
| `028000` | **Courant–Fischer min–max** (`028000-courant-fischer-min-max.md`) | Subspace dimension intersection argument and converse construction |
| `029000` | **Weyl monotonicity and variational eigenvalue inequalities** (`029000-weyl-monotonicity-and-variational-eigenvalue-inequalities.md`) | Eigenvalue order, min–max inequalities and the underlying quadratic-form comparisons |
| `030000` | **Spectral projections for selected sets** (`030000-spectral-projections-for-selected-sets.md`) | Intervals, eigenvalue clusters, projectors and reducing subspaces |
| `031000` | **Ordered gaps versus distance gaps** (`031000-ordered-gaps-versus-distance-gaps.md`) | Interlacing, internal and external gaps, block order |
| `032000` | **Coordinate-free finite functional calculus** (`032000-coordinate-free-finite-functional-calculus.md`) | Polynomial approximation and f(A) from the spectral decomposition |

### Unit V — Positive operators, modulus, polar factors, and exponentials

*Develop the constructions used throughout direct rotations, norm comparison, spectral calculus, and analytic Sylvester solutions.*

**Proof checkpoint:** Explain not just the definitions but why positive roots, partial isometries, and exponentials exist and satisfy the identities used later.

| ID | Candidate TTS lecture | Mathematical target |
| --- | --- | --- |
| `033000` | **Quadratic-form order and positive operators** (`033000-quadratic-form-order-and-positive-operators.md`) | Positivity tests, A ≥ 0, and conjugation order |
| `034000` | **Positive square roots and their uniqueness** (`034000-positive-square-roots-and-their-uniqueness.md`) | Finite proof by spectral calculus, uniqueness and commutation |
| `035000` | **The operator modulus |A|** (`035000-the-operator-modulus-a.md`) | |A|=sqrt(A* A), squared-output-length interpretation |
| `036000` | **Singular-value decomposition** (`036000-singular-value-decomposition.md`) | Singular vectors, rectangular maps, rank and kernel |
| `037000` | **Polar decomposition** (`037000-polar-decomposition.md`) | A=U|A|, initial and final supports, kernel behavior |
| `038000` | **Partial isometries and polar uniqueness** (`038000-partial-isometries-and-polar-uniqueness.md`) | When the polar factor is not unitary, restrictions and extension |
| `039000` | **Matrix exponentials from the power series** (`039000-matrix-exponentials-from-the-power-series.md`) | Why exp(A+B) requires commutation; derivative identities |
| `040000` | **Skew-adjoint generators and unitary flows** (`040000-skew-adjoint-generators-and-unitary-flows.md`) | Show exp(tK)*exp(tK)=I; planar rotations |
| `041000` | **Operator trigonometric functions** (`041000-operator-trigonometric-functions.md`) | Cosine, sine, arcsine ranges, and functional-calculus prerequisites |

### Unit VI — Geometry and classification of pairs of subspaces

*Learn how two subspaces sit inside a common Hilbert space without using arbitrary coordinate frames.*

**Proof checkpoint:** Derive principal-angle identities, two-projection blocks and the direct rotation; state the precise acute and defect hypotheses.

| ID | Candidate TTS lecture | Mathematical target |
| --- | --- | --- |
| `042000` | **Cross-Gram overlap and principal angles** (`042000-cross-gram-overlap-and-principal-angles.md`) | Singular values of V*W, unequal dimensions and canonical angles |
| `043000` | **Sines, cosines, and cross projections** (`043000-sines-cosines-and-cross-projections.md`) | P,Q, (I-Q)P and the difference of projections |
| `044000` | **The cosine–sine decomposition** (`044000-the-cosine-sine-decomposition.md`) | Two-dimensional principal planes and full complementary blocks |
| `045000` | **Halmos two-projection decomposition** (`045000-halmos-two-projection-decomposition.md`) | Common, perpendicular, defect and generic components |
| `046000` | **Positive cosine and sine operators** (`046000-positive-cosine-and-sine-operators.md`) | Compressing PQP; square roots, angle operator and spectral range |
| `047000` | **Acute pairs and transversality** (`047000-acute-pairs-and-transversality.md`) | ||P-Q||<1, invertible cosine and when graphs exist |
| `048000` | **The Sz.-Nagy–Kato intertwiner** (`048000-the-sz-nagy-kato-intertwiner.md`) | Projection algebra, polar factors and unitary transport |
| `049000` | **Canonical direct rotation** (`049000-canonical-direct-rotation.md`) | Existence, uniqueness, principal square root and adjoint reversal |
| `050000` | **Nonacute angles and defect matching** (`050000-nonacute-angles-and-defect-matching.md`) | Right-angle components, dimension obstructions and general existence |
| `051000` | **Compact angle spectra and classification** (`051000-compact-angle-spectra-and-classification.md`) | Finite/compact angle data versus continuous angle spectrum |

### Unit VII — Singular-value inequalities and symmetric norms

*Supply the finite-dimensional mathematics behind the norm generality of Davis–Kahan, not only the operator norm.*

**Proof checkpoint:** Prove rank approximation, Ky Fan bounds, a majorization principle and their consequences for symmetric gauge norms.

| ID | Candidate TTS lecture | Mathematical target |
| --- | --- | --- |
| `052000` | **Min–max principles for singular values** (`052000-min-max-principles-for-singular-values.md`) | Courant–Fischer via modulus; rectangular singular values |
| `053000` | **Low-rank approximation and Eckart–Young** (`053000-low-rank-approximation-and-eckart-young.md`) | Best rank-k approximants and tail singular-value control |
| `054000` | **Ky Fan sums and inequalities** (`054000-ky-fan-sums-and-inequalities.md`) | Partial sums, domination, subadditivity |
| `055000` | **Majorization and weak majorization** (`055000-majorization-and-weak-majorization.md`) | Finite sequences; how partial-sum comparisons control norms |
| `056000` | **Convexity and majorization descent** (`056000-convexity-and-majorization-descent.md`) | Rearrangement and convex gauge comparisons |
| `057000` | **Schatten and Frobenius norms** (`057000-schatten-and-frobenius-norms.md`) | Trace, Hilbert–Schmidt, nuclear and operator norm as examples |
| `058000` | **Unitary-invariant norms and symmetric gauges** (`058000-unitary-invariant-norms-and-symmetric-gauges.md`) | Why changing orthonormal frames leaves the size unchanged |
| `059000` | **Rectangular invariance and zero padding** (`059000-rectangular-invariance-and-zero-padding.md`) | Singular-value lists for unequal coordinate spaces |
| `060000` | **Pinching and block direct sums** (`060000-pinching-and-block-direct-sums.md`) | Reflections, block diagonal contraction, majorization-safe recombination |
| `061000` | **Quadratic-form inequalities and singular values** (`061000-quadratic-form-inequalities-and-singular-values.md`) | Trace and positive-order comparisons; limitations of passing between orders |

### Unit VIII — Sylvester equations and separated intertwiners

*Develop the operator equation that sits underneath the sine-theta proof as mathematics in its own right.*

**Proof checkpoint:** Solve AX-XB=C in scalar and matrix cases, prove a separated-spectrum estimate and distinguish ordered gaps from mere distance.

| ID | Candidate TTS lecture | Mathematical target |
| --- | --- | --- |
| `062000` | **From scalar division to AX−XB=C** (`062000-from-scalar-division-to-ax-xb-c.md`) | Spectral denominators and why gaps appear in an inverse problem |
| `063000` | **Diagonal matrices and the entrywise solution** (`063000-diagonal-matrices-and-the-entrywise-solution.md`) | When denominators vanish; uniqueness, kernel and resolvent |
| `064000` | **Kronecker sums and Sylvester invertibility** (`064000-kronecker-sums-and-sylvester-invertibility.md`) | The linear operator X ↦ AX-XB and its spectrum |
| `065000` | **Ordered spectral separation** (`065000-ordered-spectral-separation.md`) | Gap inequalities and integral solution via exponentials |
| `066000` | **Unitary and semigroup representations** (`066000-unitary-and-semigroup-representations.md`) | Differentiating e^{tA} C e^{-tB}, generators and integration |
| `067000` | **Disjoint spectral sets and Rosenblum theory** (`067000-disjoint-spectral-sets-and-rosenblum-theory.md`) | Contours and resolvent-based separated intertwiner arguments |
| `068000` | **The Banach-space Sylvester lower-bound theorem** (`068000-the-banach-space-sylvester-lower-bound-theorem.md`) | Theorem 5.1: spectral separation, inverse bounds and Banach-space operator norms |
| `069000` | **Norm dependence of Sylvester bounds** (`069000-norm-dependence-of-sylvester-bounds.md`) | Operator, Frobenius and symmetric-gauge assumptions and constants |
| `070000` | **Hilbert–Schmidt Sylvester group estimates** (`070000-hilbert-schmidt-sylvester-group-estimates.md`) | Block energy and orthogonal splitting in a Hilbert space of operators |
| `071000` | **Sylvester identities for compressed blocks** (`071000-sylvester-identities-for-compressed-blocks.md`) | The exact algebraic shape of the future residual-to-angle argument |

### Unit IX — Measure theory and spectral calculus beyond matrices

*Derive the tools needed when a self-adjoint operator does not possess an eigenvector basis.*

**Proof checkpoint:** Build the bridge from scalar measures to projection-valued measures and Borel functional calculus, including the reason polarization is required.

| ID | Candidate TTS lecture | Mathematical target |
| --- | --- | --- |
| `072000` | **Infinite-dimensional Hilbert examples** (`072000-infinite-dimensional-hilbert-examples.md`) | L2, ell2, multiplication and shift operators; continuous spectrum |
| `073000` | **Sigma-algebras and Borel sets** (`073000-sigma-algebras-and-borel-sets.md`) | Why measurable spectral sets replace finite eigenvalue lists |
| `074000` | **Measures, integration and L2** (`074000-measures-integration-and-l2.md`) | Countable additivity, convergence theorems and simple-function approximation |
| `075000` | **Continuous functional calculus and C-star identities** (`075000-continuous-functional-calculus-and-c-star-identities.md`) | Uniform approximation, spectral mapping, positive functions |
| `076000` | **Projection-valued measures** (`076000-projection-valued-measures.md`) | Countable orthogonal additivity, spectral projections and integration |
| `077000` | **Scalar spectral measures and polarization** (`077000-scalar-spectral-measures-and-polarization.md`) | The measure ⟨E(B)x,x⟩ and the complex off-diagonal pairing |
| `078000` | **Cyclic decompositions and multiplication models** (`078000-cyclic-decompositions-and-multiplication-models.md`) | Why a PVM can be represented on spaces of functions |
| `079000` | **Bounded Borel functional calculus** (`079000-bounded-borel-functional-calculus.md`) | Defining f(A) by spectral integrals and checking adjoints/products |
| `080000` | **Measurable spectral restrictions** (`080000-measurable-spectral-restrictions.md`) | Spectral selection, naturality, restriction and commutation |
| `081000` | **Resolvents from spectral integrals** (`081000-resolvents-from-spectral-integrals.md`) | Recovering the spectrum from inverse bounds and spectral support |
| `082000` | **Spectral approximation by cutoffs** (`082000-spectral-approximation-by-cutoffs.md`) | Finite partitions and passage to strong limits |

### Unit X — Closed and unbounded self-adjoint operators

*Replace illegal informal matrix manipulations with domain-correct operator equalities and controlled limits.*

**Proof checkpoint:** Construct closed-operator, adjoint, resolvent and spectral-cutoff arguments well enough to prove the unbounded Sylvester estimates used in the full source theorem.

| ID | Candidate TTS lecture | Mathematical target |
| --- | --- | --- |
| `083000` | **Densely defined operators and their graphs** (`083000-densely-defined-operators-and-their-graphs.md`) | Domain as part of the operator; graph norm and closedness |
| `084000` | **Adjoints of unbounded operators** (`084000-adjoints-of-unbounded-operators.md`) | Symmetric versus self-adjoint; adjoint domains |
| `085000` | **Hellinger–Toeplitz and common-domain discipline** (`085000-hellinger-toeplitz-and-common-domain-discipline.md`) | Why everywhere-defined self-adjoint maps are bounded |
| `086000` | **Resolvents, coercivity, and spectral location** (`086000-resolvents-coercivity-and-spectral-location.md`) | Real form bounds, resolvent norms, invertibility |
| `087000` | **Cayley transforms and graph-level equivalence** (`087000-cayley-transforms-and-graph-level-equivalence.md`) | Turning unbounded self-adjoint operators into bounded unitary data |
| `088000` | **Unbounded spectral theorem and domain calculus** (`088000-unbounded-spectral-theorem-and-domain-calculus.md`) | Spectral integrals with integrability constraints on vectors |
| `089000` | **Spectral projections and reducing domains** (`089000-spectral-projections-and-reducing-domains.md`) | When a reducing subspace respects an unbounded domain |
| `090000` | **Quadratic forms and ordered half-infinite gaps** (`090000-quadratic-forms-and-ordered-half-infinite-gaps.md`) | Semibounded operators, form inequalities and gap alternatives |
| `091000` | **Yosida approximation and bounded truncations** (`091000-yosida-approximation-and-bounded-truncations.md`) | Regularization while retaining self-adjoint structure |
| `092000` | **One-parameter unitary groups and their generators** (`092000-one-parameter-unitary-groups-and-their-generators.md`) | Strong continuity and Stone-style generator correspondence |
| `093000` | **Domain-aware Sylvester identities and cutoffs** (`093000-domain-aware-sylvester-identities-and-cutoffs.md`) | Proof of block identities before estimating their bounded extensions |
| `094000` | **Unbounded Sylvester estimates** (`094000-unbounded-sylvester-estimates.md`) | Half-infinite ordered gaps, spectral restrictions and limiting arguments |

### Unit XI — Infinite-dimensional operator ideals and real/complex transfer

*Make the symmetric-norm assertions legal, and cover the real Hilbert statements without presuming every complex theorem transfers automatically.*

**Proof checkpoint:** Explain why an ideal norm can be undefined outside its domain, how approximation-number inequalities descend, and how real operators can be complexified and recovered.

| ID | Candidate TTS lecture | Mathematical target |
| --- | --- | --- |
| `095000` | **Compactness and finite-rank approximation** (`095000-compactness-and-finite-rank-approximation.md`) | Compact operators, strong versus norm convergence, approximation |
| `096000` | **Approximation numbers and singular-value sequences** (`096000-approximation-numbers-and-singular-value-sequences.md`) | Finite matrix analogy and infinite-dimensional definitions |
| `097000` | **Ky Fan dominance in Hilbert space** (`097000-ky-fan-dominance-in-hilbert-space.md`) | Approximation sequences and norming functions |
| `098000` | **Symmetric operator ideals and membership** (`098000-symmetric-operator-ideals-and-membership.md`) | Where-defined gauges and why not every bounded map has finite ideal norm |
| `099000` | **Hilbert–Schmidt and trace-class operators** (`099000-hilbert-schmidt-and-trace-class-operators.md`) | Operator inner products, bases, nuclear traces and finite-rank density |
| `100000` | **Modulus, polar factors, and ideal invariance** (`100000-modulus-polar-factors-and-ideal-invariance.md`) | Rectangular operator transport without assuming invertibility |
| `101000` | **Ideal estimates for compressions and block sums** (`101000-ideal-estimates-for-compressions-and-block-sums.md`) | Membership preservation, pinching and direct sums |
| `102000` | **Real Hilbert complexification** (`102000-real-hilbert-complexification.md`) | Construction, norms and how linear/adjoint operations commute with transfer |
| `103000` | **Real and complex spectra and functional calculus** (`103000-real-and-complex-spectra-and-functional-calculus.md`) | Transport and descent of self-adjoint spectral assertions |
| `104000` | **Real versions of unbounded Sylvester bounds** (`104000-real-versions-of-unbounded-sylvester-bounds.md`) | Domains, resolvents and transferred estimates |
| `105000` | **A full proof-readiness assembly** (`105000-a-full-proof-readiness-assembly.md`) | Reconstruct the analytic lemma stack for a symmetric-norm, unbounded sine estimate |

### Unit XII — Entering perturbation theory: residual geometry and single angles

*Now ask the stability question, with a full repertoire of spaces, spectral objects, norm systems, and inverse-operator tools.*

**Proof checkpoint:** Starting from a 2x2 example, derive the complete residual-to-complementary-Sylvester-to-sine chain and its tangent counterpart.

| ID | Candidate TTS lecture | Mathematical target |
| --- | --- | --- |
| `106000` | **What changes and what stays invariant** (`106000-what-changes-and-what-stays-invariant.md`) | A two-level counterexample, stable clusters, and the first perturbation question |
| `107000` | **Trial spaces, exact subspaces and residuals** (`107000-trial-spaces-exact-subspaces-and-residuals.md`) | Trial isometries, compressed operators and A E−E A0 |
| `108000` | **The complementary-block Sylvester equation** (`108000-the-complementary-block-sylvester-equation.md`) | Exact reducing coordinates and F1*R=Λ1 X−X A0 |
| `109000` | **Directed sine as a rectangular modulus** (`109000-directed-sine-as-a-rectangular-modulus.md`) | S=(I−P)E, |S|=sin Θ0 and its coordinate independence |
| `110000` | **The single-angle sine theorem** (`110000-the-single-angle-sine-theorem.md`) | Spectral separation, ideal contraction, membership and full hypotheses |
| `111000` | **Graph subspaces and tangent geometry** (`111000-graph-subspaces-and-tangent-geometry.md`) | Acute pairs, graph operators and tan Θ |
| `112000` | **The single-angle tangent theorem** (`112000-the-single-angle-tangent-theorem.md`) | Ordered separation, proof mechanism and limit as angles approach 90 degrees |
| `113000` | **Sharp examples and norm-class comparisons** (`113000-sharp-examples-and-norm-class-comparisons.md`) | How gaps, residuals and constants can fail or become optimal |

### Unit XIII — Double-angle estimates, reflections, and branch choice

*Develop the other two headline theorem families and the selection theory that gives them an interpretable small-angle meaning.*

**Proof checkpoint:** Use block reflections to derive double-angle expressions; exhibit the ambiguity of sin(2 theta) and prove spectral selection criteria.

| ID | Candidate TTS lecture | Mathematical target |
| --- | --- | --- |
| `114000` | **Off-diagonal perturbations and block reflection** (`114000-off-diagonal-perturbations-and-block-reflection.md`) | P H P=0 and complementary diagonal blocks; anticommutation |
| `115000` | **Doubled angles from symmetry** (`115000-doubled-angles-from-symmetry.md`) | Why reflection compares geometric data with its transformed copy |
| `116000` | **The sine-two-theta theorem** (`116000-the-sine-two-theta-theorem.md`) | Full operator-angle interpretation, constants and norms |
| `117000` | **The tangent-two-theta theorem** (`117000-the-tangent-two-theta-theorem.md`) | Ordered separation, Riccati/graph picture and quarter-turn boundary |
| `118000` | **Why a small doubled sine proves little alone** (`118000-why-a-small-doubled-sine-proves-little-alone.md`) | Near-zero and near-right-angle branches |
| `119000` | **Spectral selection and repulsion** (`119000-spectral-selection-and-repulsion.md`) | Theorem 8.1, its block inequalities and unique reducing branch |
| `120000` | **Small-angle certification** (`120000-small-angle-certification.md`) | Theorem 8.2 and safe branch thresholds |
| `121000` | **A comparative theorem decision procedure** (`121000-a-comparative-theorem-decision-procedure.md`) | Four bounds, three gap regimes, directed versus full angles |

### Unit XIV — Generalized bounds and source-faithful norm estimates

*Complete Section 6 and the auxiliary norm, pinching, and finite-rank results not captured by the four headlines.*

**Proof checkpoint:** Prove the generalized theorems with dimension mismatch and frame defects; distinguish each original hypothesis from a merely convenient stronger assumption.

| ID | Candidate TTS lecture | Mathematical target |
| --- | --- | --- |
| `122000` | **Direct-sum norm comparison** (`122000-direct-sum-norm-comparison.md`) | Lemma 6.1 and rank-safe weak majorization |
| `123000` | **Pinching through an involution** (`123000-pinching-through-an-involution.md`) | Lemma 6.2 and block-diagonal contraction |
| `124000` | **Ambient sine from an ambient perturbation** (`124000-ambient-sine-from-an-ambient-perturbation.md`) | Proposition 6.1 versus a directed residual |
| `125000` | **Non-isometric frames and unequal dimensions** (`125000-non-isometric-frames-and-unequal-dimensions.md`) | Theorem 6.1, lower frame bound and epsilon |
| `126000` | **Weak spectral gaps and Hilbert–Schmidt estimates** (`126000-weak-spectral-gaps-and-hilbert-schmidt-estimates.md`) | Theorem 6.2 and what fails without ordered separation |
| `127000` | **The generalized tangent bound** (`127000-the-generalized-tangent-bound.md`) | Theorem 6.3, Rayleigh–Ritz and frame geometry |
| `128000` | **Spectral cutoff and finite-rank source lemmas** (`128000-spectral-cutoff-and-finite-rank-source-lemmas.md`) | Section 5.1 and 6.3 lemmas; why their hypotheses matter |
| `129000` | **One complete original-paper proof reconstruction** (`129000-one-complete-original-paper-proof-reconstruction.md`) | Choose one hard result and rederive every analytic dependency |

### Unit XV — Direct-rotation extremals and corrected optimality

*Treat the rotation optimization mathematics on its own terms, rather than assuming canonical transport is universally optimal.*

**Proof checkpoint:** Derive exact restricted and squared displacement claims, calculate the counterexample, and isolate the corrected theorem.

| ID | Candidate TTS lecture | Mathematical target |
| --- | --- | --- |
| `130000` | **Restricted direct-rotation optimality** (`130000-restricted-direct-rotation-optimality.md`) | Proposition 4.1 and Corollary 4.1 via singular-angle inequalities |
| `131000` | **The squared displacement of orthonormal frames** (`131000-the-squared-displacement-of-orthonormal-frames.md`) | Proposition 4.2 and how errors add |
| `132000` | **Whole-space squared displacement and Q-norms** (`132000-whole-space-squared-displacement-and-q-norms.md`) | Proposition 4.3 and the exact family of objectives |
| `133000` | **Unsquared ambient displacement is different** (`133000-unsquared-ambient-displacement-is-different.md`) | The optimization problem printed as Proposition 4.4 |
| `134000` | **The four-dimensional real counterexample** (`134000-the-four-dimensional-real-counterexample.md`) | Competing rotation, trace norm, singular-value comparison |
| `135000` | **Corrected scopes and surviving results** (`135000-corrected-scopes-and-surviving-results.md`) | Restricted optimality and valid norm-specific statements |
| `136000` | **Classification and realizations of direct rotations** (`136000-classification-and-realizations-of-direct-rotations.md`) | Defects, compact angle data and boundary cases revisited |

### Unit XVI — Worked original-paper calculation and open problems

*Apply the theory to the source paper numerical example, then reconstruct its research questions as mathematical problems.*

**Proof checkpoint:** Work through the free-beam model and the bounds instead of quoting a table of numerical constants.

| ID | Candidate TTS lecture | Mathematical target |
| --- | --- | --- |
| `137000` | **The free-beam operator and its domain** (`137000-the-free-beam-operator-and-its-domain.md`) | Fourth-order differential operator, boundary conditions and Green identities |
| `138000` | **Beam Rayleigh–Ritz calculation** (`138000-beam-rayleigh-ritz-calculation.md`) | Trial functions, compressed matrix and residual |
| `139000` | **Comparing angle and Ky Fan beam estimates** (`139000-comparing-angle-and-ky-fan-beam-estimates.md`) | Source Section 9 numerical inequalities and their improvements |
| `140000` | **From subspace bounds to individual modes** (`140000-from-subspace-bounds-to-individual-modes.md`) | Internal gaps, complement blocks and Schur-type reductions |
| `141000` | **How much can a distance-only gap say** (`141000-how-much-can-a-distance-only-gap-say.md`) | Question 10.1 with known cases and counterexamples |
| `142000` | **Three subspaces and higher-order interactions** (`142000-three-subspaces-and-higher-order-interactions.md`) | Question 10.2 and block geometry |
| `143000` | **Joint movement of eigenvalues and angles** (`143000-joint-movement-of-eigenvalues-and-angles.md`) | Question 10.3, motivations and obstacles |
| `144000` | **Stability of functions of operators** (`144000-stability-of-functions-of-operators.md`) | Question 10.4 and the need for functional calculus |

### Unit XVII — Companion formalizations and independent proof mastery

*Use the infrastructure to understand adjacent mathematical consequences without mistaking them for requirements of the original 1970 result census.*

**Proof checkpoint:** Prove a modern singular-subspace or statistical bound and independently reconstruct one full 1970 theorem from stated analytic foundations.

| ID | Candidate TTS lecture | Mathematical target |
| --- | --- | --- |
| `145000` | **From rotation counterexample to real transport matching** (`145000-from-rotation-counterexample-to-real-transport-matching.md`) | Trace-norm matching and principal-plane coupling |
| `146000` | **Rectangular singular-subspace bounds** (`146000-rectangular-singular-subspace-bounds.md`) | Hermitian dilation, Gram perturbation and Wedin-type phenomena |
| `147000` | **Population-gap spectral statistics** (`147000-population-gap-spectral-statistics.md`) | Yu–Wang–Samworth versus mixed sample/population gap |
| `148000` | **Procrustes and spectral embeddings** (`148000-procrustes-and-spectral-embeddings.md`) | Aligned eigenframes, Gram rigidity and downstream representation error |
| `149000` | **Proof practicum: reconstruct the 1970 theory** (`149000-proof-practicum-reconstruct-the-1970-theory.md`) | Write a coherent finite-to-infinite proof pathway; check full source hypotheses |

## Original 1970 source-result coverage (29-result endpoint map)

This crosswalk uses the repository’s selected original-paper result IDs. A row shows the **planned teaching location**, not a claim that the lecture or a new Lean proof exists. The full statement and hypotheses belong in `papers/dk_formalization_journal/appendix_result_summaries.tex`. The 1970 result list must **not** be mistaken for the total mathematical prerequisite set.

| 1970 result | Mathematical statement | Planned lecture slot(s) |
| --- | --- | --- |
| `S2-sin-theta` | Single-angle sine theorem | `110000`, `105000` |
| `S2-tan-theta` | Single-angle tangent theorem | `112000`, `127000` |
| `S2-sin-two-theta` | Double-angle sine theorem | `116000` |
| `S2-tan-two-theta` | Double-angle tangent theorem | `117000` |
| `DK-3.1-prop` | Acute direct rotation existence and uniqueness | `049000` |
| `DK-3.2-prop` | Nonacute existence criterion | `050000` |
| `DK-3.3-prop` | Principal square-root characterization | `049000`, `046000` |
| `DK-3.4-prop` | Square as a direct rotation | `049000` |
| `DK-3.1-thm` | Classification of pairs of subspaces | `050000` |
| `DK-3.1-cor` | Compact classification by angle eigenvalues | `051000`, `136000` |
| `DK-3.5-prop` | Angle commutation and eigenspace geometry | `049000`, `046000` |
| `DK-3.2-cor` | Reversal symmetry | `049000` |
| `DK-4.1-prop` | Pointwise and singular-value extremality of the direct rotation | `130000` |
| `DK-4.1-cor` | UI-norm minimality of direct rotation displacement | `130000` |
| `DK-4.2-prop` | Basis-angle square-sum extremality | `131000` |
| `DK-4.3-prop` | Squared displacement UI-norm minimality | `132000` |
| `DK-4.4-prop` | Full-displacement counterexamples and Proposition 4.4 as printed | `133000`, `134000` |
| `DK-5.1-thm` | Banach-space Sylvester lower bound | `068000` |
| `DK-5.2-thm` | Semibounded self-adjoint Sylvester theorem | `094000` |
| `DK-5.1-lem` | Strong-cutoff convergence of singular values | `082000`, `128000` |
| `DK-6.1-lem` | Direct-sum UI-norm comparison and converse | `122000` |
| `DK-6.2-lem` | Reflection-pinch contraction | `123000` |
| `DK-6.1-prop` | Sine proof, ambient limitation, and symmetric sine theorem | `124000` |
| `DK-6.1-thm` | Generalized sine theorem | `125000` |
| `DK-6.2-thm` | Pairwise-gap square-norm sine theorem | `126000` |
| `DK-6.3-thm` | Tangent proof machinery, Example 6.1, and generalized tangent theorem | `127000` |
| `DK-6.3-lem` | Finite-rank near-maximizer leakage estimate | `128000` |
| `DK-8.1-thm` | Branch selection and spectral repulsion | `119000` |
| `DK-8.2-thm` | Smallness selects the acute branch | `120000` |

## Proof-dependency coverage beyond the 29 original source results

The journal paper's dependency analysis (`papers/dk_formalization_journal/data/formalization_theory_taxonomy_20260817.json`, with source-root/declaration traces) recognizes reusable mathematical foundations not counted as source theorems. The following is a **mathematical** coverage checklist, independent of the present locations of Lean files.

| Required machinery | Course units | Why it is load-bearing | Evidence to consult during drafting |
| --- | --- | --- | --- |
| Banach/Hilbert completeness, bounded maps, Riesz, subspaces, adjoints | I–II | Legal operator norms, inverses, adjoints and closed subspaces | Mathlib foundations; `ForTauCeti/Analysis/InnerProductSpace/Basic.lean` |
| Frame synthesis/analysis, isometries, Gram and cross-Gram operators | II–III | Trial coordinate spaces, compressed blocks and rectangular residuals | `ForTauCeti/Analysis/InnerProductSpace/FiniteFrame.lean`; `.../AlignedBasis.lean` |
| Self-adjoint spectral theorem, Courant–Fischer, Weyl, Ritz | IV | Exact spectral blocks, ordered gaps and variational estimates | `ForTauCeti/Analysis/InnerProductSpace/Spectral/EigenFrame.lean`; `.../Residual/Ritz.lean`; TauCeti accepted min–max modules (verify pin) |
| Positive square roots, modulus, polar and partial isometries, operator exponentials | V | Canonical direct rotation, sine-angle modulus, norm invariance, spectral flows | `ForTauCeti/Analysis/CStarAlgebra/PositiveSquareRootCommute.lean`; `ForTauCeti/Analysis/InnerProductSpace/SkewAdjointExponential.lean`; TauCeti polar APIs (verify pin) |
| Two-projection, cosine/sine and Halmos classification | VI | Full and directed angles, acute/nonacute existence and rotation uniqueness | `DavisKahan/Geometry/Halmos/TwoProjections.lean`; `ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean` |
| Approximation numbers, Ky Fan, majorization, UINs | VII, XI | Every-norm/where-defined interpretation of the original statements | `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/`; `ForTauCeti/Analysis/Convex/Majorization.lean` |
| Sylvester, Rosenblum, semigroups, ordered and separated gaps | VIII, X | The inverse problem turning a residual into an angle inequality | `ForTauCeti/Analysis/InnerProductSpace/Sylvester/`; `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean` |
| Measure theory, PVM, Borel spectral calculus and polarization | IX | Spectral subspaces with continuous spectrum; spectral cutoffs | `ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/`; `.../ProjValMeasure/`; TauCeti imported PVM modules (verify pin) |
| Closed/unbounded self-adjoint domains, resolvents, graph and spectral cutoffs | X | Full unbounded Hilbert-space theorem rather than bounded-matrix substitute | `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean`; `.../YosidaApproximation.lean`; `.../Resolvent.lean` |
| Complexification and real spectral descent | I, XI | Prove claims for real and complex Hilbert spaces without a silent field restriction | `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Complexification.lean`; `.../RealSpectrumBorelSymbols.lean` |
| Spectral residuals and full four angle families | XII–XIV | Actual original-paper theorems, assumptions, exact norm scope | `DavisKahan/Sources/DavisKahan1970/`; `DavisKahan/Sylvester/Gap.lean` |
| Direct-rotation objective and correction | VI, XV, XVII | Distinguish restricted displacement from false full trace-norm minimality | `DavisKahan/FiniteDimensional/DirectRotation/`; `papers/optimal_spectral_transport/` |
| Free-beam realization and form analysis | X, XVI | Source Section 9 worked example, including an unbounded fourth-order operator | `ForTauCeti/Analysis/Calculus/FourthOrderGreensIdentity.lean`; original Section 9 reconstruction |
| Rectangular singular-subspaces, population gaps, Procrustes | III, VII, XVII | Companion formalizations and downstream applications | `ForTauCeti/Analysis/InnerProductSpace/Singular/Subspace.lean`; `YuWangSamworth/` source where available |

### Upstream preservation rule

Some foundations were **developed or substantially adapted in this repository** and later consumed from TauCeti. A missing local donor file therefore does **not** imply that the mathematics is irrelevant. The maintained `dev/tauceti/dkps-upstream-contribution-census.md` is the starting point for the lineage audit; `dev/tauceti/roadmap-topic-map.md` identifies the broad families (polar decomposition, orthogonal geometry, majorization, principal angles, ideals, self-adjoint spectral theory, spectral subspace perturbation, and matrix spectral statistics). The provenance record also distinguishes DKPS donors, Spectra ancestry, independent TauCeti proofs, and roadmap-associated work—these are not interchangeable authorship claims.

The independent source is the **mathematical dependency**, not the old import graph, PR count, or whatever module currently owns a declaration. When preparing a lesson, check current dependencies and matched declarations in the target repository; the uploaded snapshot does not include an accessible checkout of every pinned TauCeti source file.

### Deep proof-reconstruction assessments

These are not additional mandated videos. They are summative tasks: students should be able to carry them out with earlier lectures, rather than merely quote a named lemma.

1. **Projection/polar construction:** Starting from closed subspaces and their projections, derive cosine and sine operators, construct the acute direct rotation, and account for defects in a nonacute example.
2. **Analytic Sylvester construction:** Starting with separated self-adjoint blocks, establish an inverse estimate for `AX-XB=C` in an appropriate norm. Repeat with ordered unbounded form gaps and explain why domains/cutoffs are necessary.
3. **Spectral calculus:** Starting from scalar measures and the PVM axioms, explain how `f(A)` and a spectral projection are constructed; treat a multiplication operator whose spectrum is not exhausted by eigenvalues.
4. **Norm generality:** Prove a Ky Fan bound, pass it to a symmetric-gauge inequality under the required assumptions, and state explicitly when ideal membership is needed.
5. **Full sine-theta proof:** State trial/exact subspaces and domains, derive `F1*R=Λ1 X-XA0`, identify `|X|` as the directed sine, then prove the **where-defined** unitarily invariant inequality. Explain real/complex transfer.
6. **Other three angle theorems:** Reconstruct the tangent and double-angle arguments, state actual gap hypotheses, and resolve branch ambiguity through spectral selection.
7. **Original paper closure:** Reprove the Section 3–6 and Section 8 source-result families, analyze Proposition 4.4's counterexample, and reproduce the beam example and Section 10 questions.

## Backward proof-chain map (for course auditing)

A complete sine-theta proof must pass through the following chain; each arrow is a mathematical obligation, *not* automatically established by mentioning an API:

```
Hilbert/operator foundations + spectral calculus + domains
        |                          |
        v                          v
trial and exact isometries     reducing spectral subspaces
        |                          |
        +----> R = A E0 - E0 A0 <--+
                       |
                       v
       F1*R = Lambda1 X - X A0   (domain-aware)
                       |
                 spectral gap
                       |
                       v
            delta N(X) <= N(F1*R)
                       |
        ideal membership + contraction
                       |
                       v
                <= N(R)
                       |
      |X| = sin(Theta0) + modulus invariance
                       |
                       v
            delta N(sin Theta0) <= N(R)
```

To recover other theorems, add graph/tangent geometry, reflections and double-angle calculus, branch selection, direct-rotation geometry, and (for Section 6) dimension mismatch and pinching. This is the conceptual dependency map the old lecture inventory was not designed to supply.

## Explicit next drafting stages

- **Stage 0 — architecture:** review this expanded mathematical dependency map against the journal paper, the source result summaries, the theory taxonomy, and the recorded upstream ancestry. Preserve the 29-result table but audit proof dependencies beyond it.
- **Stage 1 — orientation:** use `tts-lectures/000000-course-introduction.md`. It promises the course, establishes expectations and gives a concrete idea of *why* the mathematical machinery is needed. **No Lean excerpt is required and none is included.**
- **Stage 2 — foundations:** draft Units I–III as a connected audio-first sequence, with actual examples, proof arguments and verified final symbol-to-Lean bridges for substantive topics. Then progress through the remaining foundations before the stability chapter.
- **Stage 3 — independent readiness checks:** have a reviewer attempt the seven assessments above using only the completed lessons; add missing prerequisites when proof steps cannot be reconstructed.
- **Stage 4 — visualizations:** storyboard and produce Manim as a derived presentation. Keep a transcript that works without visuals. This alternative proposal does not change the existing lecture registry.

## References and audit starting points

- `papers/dk_formalization_journal/paper.tex`, especially “Foundations used in our formalization,” “Formalized operator-theoretic foundations,” and the Section 2 sine-theta derivation.
- `papers/dk_formalization_journal/data/formalization_theory_taxonomy_20260817.json` and `.../formalization_theory_evidence_links_20260817.csv` (curated mathematical classification).
- `papers/what_it_takes_to_prove_davis_kahan/cases/sine_theta.md` (explicit theorem-level proof chain).
- `dev/davis-kahan-1970-formalization-result-inventory.json` and `papers/dk_formalization_journal/appendix_result_summaries.tex` (29 source results).
- `dev/tauceti/dkps-upstream-contribution-census.md`, `dev/tauceti/roadmap-topic-map.md`, and `dev/tauceti/spectra-provenance-map.md` (mathematical ancestry and where foundations now reside).
- `papers/dk_formalization_journal/scripts/build_formalization_prerequisite_trace.py` and `.../build_formalization_theory_graph.py` (compiler-derived proof dependency trace joined to mathematical topic classifications; use the saved artifacts when a live Lean environment is unavailable).
- `prose/distilled_literature/DavisKahan1970_part_III.tex` (original-paper section reconstruction).
- `visualizations/lectures/LEAN_FACTS.md` and `visualizations/lectures/*/facts.lean` (legacy Lean-bridge design reference, **not** syllabus authority).
