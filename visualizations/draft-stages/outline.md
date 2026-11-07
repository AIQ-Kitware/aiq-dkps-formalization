# Proposed transcript-first course — staged drafting track

**Status:** alternative direction / course-outline draft, not the active lecture registry.
**Working title:** *The Geometry and Stability of Spectral Subspaces*.
**Scope:** mathematical content and applications; **history lectures are excluded** and remain on their own planning track.

## Purpose and separation

This is a parallel proposal, not a migration of `visualizations/lectures/`.
Keep all existing numbered lectures, `lectures/index.yaml`, decks, Manim scenes,
TTS orchestration, and historical lectures unchanged while we evaluate the
transcript-first direction. Nothing in this directory is currently registered
for production. Do **not** render this directory by assuming it has the same
structure as the existing `lectures/` tree.

The teaching problem is: **when an operator changes, what can we say about its
eigenvalues, eigenspaces, and geometric structure?** The course should first
make this problem intelligible with small matrices, then build the mathematics
needed to solve it, and finally recover the actual operator-theoretic scope of
the Davis–Kahan paper and relevant extensions. The historical chronology is
not the dependency ordering of the course.

**Authoring principle:** mathematical references determine what is true;
**the spoken transcript determines how the learner comes to understand it**;
visualizations are derived from the explanatory narrative. A complete lecture
must work when heard without any screen. An animation is justified by the
mathematical understanding it adds, not by a requirement to animate every
sentence.

## Draft stages

1. **Course map.** Maintain this document as the proposed scope, teaching order,
   open questions, and coverage links. Titles and positions are provisional.
2. **Audio-first draft.** Write a complete, self-contained spoken explanation
   under `tts-lectures/NNNNNN-topic-slug.md`. This is real lecture prose, not
   scene notes, slide copy, or a script forced into animation beats.
3. **Conceptual edit by listening.** Hear the transcript in continuous audio;
   repair unmotivated concepts, hidden reasoning, rushed derivations, or passages
   that presume an unseen picture. Revise prose *before* storyboarding scenes.
4. **Mathematical review.** Check important claims, hypotheses, examples,
   constants, norm choices, countermodels, and source correspondence against
   primary mathematics and applicable Lean results. An explanatory example is
   not itself a proof of a general theorem.
5. **Semantic visual plan.** Identify points where a picture, animation,
   equation highlight, numerical example, or silence improves an already
   coherent narration. Anchor visuals to concepts/passages; do not re-segment
   the narrative merely to fit slides.
6. **Implementation and evaluation.** Only after acceptance, integrate Manim,
   TTS, captions, sources, exercises, and optional Lean companions using the
   existing production system (or a separately reviewed adapter). Check the
   *listening* and *viewing* experiences independently.

Stages 3 and 4 can iterate in either order. Do not regard "drafted" as
"mathematically reviewed" or "TTS rendered". The draft track deliberately
adds **no new automation, registries, build gates, or generated media**.

### Editorial contract for `tts-lectures/`

- Six-digit increasing numeric prefix, **1,000 apart** in this proposed
  sequence. `000000` is the course introduction. Numbers are ordering handles,
  not course identity; gaps allow insertions without renumbering existing drafts.
- One standalone lecture per Markdown file. Use a short top-level title and
  section headings to help a human edit it; **the spoken material is the prose
  paragraphs, not the headings**. A future TTS adapter must explicitly define
  how it strips editorial structure rather than silently reading it aloud.
- Write for listening. Explain notation in speech. The narration must not say
  "as you can see" or rely on a diagram, slide, earlier chat, or repository
  structure to carry its reasoning. Prefer coherent paragraphs to short,
  separately synthesized visual beats.
- Maintain precision: distinguish an eigengap of the original operator from
  the certified cross-spectral separation needed by a particular theorem;
  distinguish individual eigenvectors from invariant subspaces; identify
  norm and domain hypotheses where they matter.
- Do not put model attribution, source catalogs, Manim instructions, Lean
  listings, or mathematical TODOs into the *spoken* text. Keep such material
  here in the planning document until a separate source-note mechanism is
  needed. Optional exercises and formal companions can be added later.
- A transcript may be split or merged after listening review. Update this
  outline when that happens; do not force pedagogical decisions to preserve
  the first numbering proposal.

## Curriculum map

`000000-course-introduction.md` is the **only written transcript in this
first overlay**. Its job is to make the course's guiding question meaningful,
not to prove the angle theorems. Everything below is planned, not written.

| Order | Lecture | Core teaching result |
| --- | --- | --- |
| `000000` | **Course introduction** — `000000-course-introduction.md` (**draft v1**) | Why spectral stability is a problem, which objects are worth tracking, and how the course will approach it. |

### Unit I — Why spectral stability matters

*Establish the question and make the failure mode tangible.*

| Order | Proposed lecture | What the learner should understand |
| --- | --- | --- |
| `001000` | When eigenvectors suddenly move (`001000-when-eigenvectors-suddenly-move.md`) | A two-by-two counterexample; perturbation size versus eigenvalue gap. |
| `002000` | The mathematical toolkit (`002000-the-mathematical-toolkit.md`) | Vectors, matrices, spectra, orthogonality, adjoints, and basic calculus as an optional refresher. |


### Unit II — The geometry of subspaces

*Learn to compare spaces without depending on arbitrary choices of basis.*

| Order | Proposed lecture | What the learner should understand |
| --- | --- | --- |
| `003000` | Subspaces and orthogonal projections (`003000-subspaces-and-orthogonal-projections.md`) | Subspaces as geometric objects and projectors as algebraic encodings. |
| `004000` | Invariant and reducing subspaces (`004000-invariant-and-reducing-subspaces.md`) | How an operator preserves a subspace and when block decompositions are justified. |
| `005000` | What does I minus P measure? (`005000-what-does-i-minus-p-measure.md`) | Complementary projections, perpendicular error, and directed distance. |
| `006000` | Singular values and matrix norms (`006000-singular-values-and-matrix-norms.md`) | SVD, operator and Frobenius norms, Schatten norms, and Ky Fan sums. |
| `007000` | Principal angles between subspaces (`007000-principal-angles-between-subspaces.md`) | The angle spectrum of two subspaces and its relation to projection distances. |
| `008000` | The canonical two-subspace decomposition (`008000-the-canonical-two-subspace-decomposition.md`) | Principal planes, cosine-sine blocks, intersection and defect pieces. |
| `009000` | Polar decomposition and alignment (`009000-polar-decomposition-and-alignment.md`) | Splitting a map into a positive part and a partial isometry; aligning frames. |


### Unit III — Spectral stability and residuals

*Turn approximate spectral information into quantitative guarantees.*

| Order | Proposed lecture | What the learner should understand |
| --- | --- | --- |
| `010000` | Rayleigh quotients and eigenvalue approximation (`010000-rayleigh-quotients-and-eigenvalue-approximation.md`) | Quadratic forms and approximate eigenvalues. |
| `011000` | Courant-Fischer, min-max, and Weyl stability (`011000-courant-fischer-min-max-and-weyl-stability.md`) | Variational eigenvalue bounds and why they do not imply stable eigenvectors. |
| `012000` | Rayleigh-Ritz and trial subspaces (`012000-rayleigh-ritz-and-trial-subspaces.md`) | Compression, Ritz vectors, and the role of a trial space. |
| `013000` | Residuals and spectral gaps (`013000-residuals-and-spectral-gaps.md`) | What approximate invariance measures and why separation matters. |
| `014000` | From scalar division to Sylvester equations (`014000-from-scalar-division-to-sylvester-equations.md`) | From ax minus xb equals c to matrix and operator equations. |
| `015000` | Sylvester estimates and their limitations (`015000-sylvester-estimates-and-their-limitations.md`) | Spectral-set separation, order assumptions, and the dependence on norm type. |


### Unit IV — How to move one subspace onto another

*Construct the canonical motion rather than merely compare endpoints.*

| Order | Proposed lecture | What the learner should understand |
| --- | --- | --- |
| `016000` | Matrix exponentials and continuous rotations (`016000-matrix-exponentials-and-continuous-rotations.md`) | Skew-adjoint generators and unitary/orthogonal flows. |
| `017000` | The direct rotation (`017000-the-direct-rotation.md`) | Constructing canonical motion from projections and principal-angle blocks. |
| `018000` | Existence, uniqueness, and exceptional cases (`018000-existence-uniqueness-and-exceptional-cases.md`) | Acute pairs, right-angle parts, dimensional obstructions, and scope of uniqueness. |


### Unit V — The four Davis-Kahan angle-theorem families

*Understand what each bound measures and the hypotheses it genuinely needs.*

| Order | Proposed lecture | What the learner should understand |
| --- | --- | --- |
| `019000` | The sine-theta theorem: geometric intuition (`019000-the-sine-theta-theorem-geometric-intuition.md`) | Perpendicular residual versus certified spectral separation. |
| `020000` | The sine-theta theorem: the proof (`020000-the-sine-theta-theorem-the-proof.md`) | Block equations and valid norm-dependent estimates. |
| `021000` | Why a tangent bound is different (`021000-why-a-tangent-bound-is-different.md`) | Graph coordinates and the meaning of the tangent of a subspace angle. |
| `022000` | The tangent-theta theorem (`022000-the-tangent-theta-theorem.md`) | Ordered separation, theorem hypotheses, and a proof route. |
| `023000` | Off-diagonal perturbations and reflection symmetry (`023000-off-diagonal-perturbations-and-reflection-symmetry.md`) | The structural origin of doubled angles. |
| `024000` | The sine-two-theta theorem (`024000-the-sine-two-theta-theorem.md`) | Reflection-based geometry, bounds, and their domains of validity. |
| `025000` | The tangent-two-theta theorem (`025000-the-tangent-two-theta-theorem.md`) | Additional off-diagonal hypotheses, branches, and the quarter-turn boundary. |
| `026000` | Choosing the right theorem (`026000-choosing-the-right-theorem.md`) | Compare residuals, gaps, norms, branches, constants, and counterexamples. |


### Unit VI — Optimal rotations and matching

*Ask not only how much a subspace moves, but what it costs to move it.*

| Order | Proposed lecture | What the learner should understand |
| --- | --- | --- |
| `027000` | What makes the direct rotation optimal? (`027000-what-makes-the-direct-rotation-optimal.md`) | Restricted displacement objectives and the relevant optimization claim. |
| `028000` | Restricted versus whole-space displacement (`028000-restricted-versus-whole-space-displacement.md`) | Why a minimizer for a restricted cost need not minimize another cost. |
| `029000` | A counterexample to Proposition 4.4 (`029000-a-counterexample-to-proposition-4.4.md`) | A real four-dimensional counterexample to the printed statement. |
| `030000` | The correct optimality statements (`030000-the-correct-optimality-statements.md`) | Qualified replacement results with their specific norm and scope. |
| `031000` | Trace pairings and matrix gradients (`031000-trace-pairings-and-matrix-gradients.md`) | Scalar matrix objectives and first variation. |
| `032000` | Feasible variations and stationarity (`032000-feasible-variations-and-stationarity.md`) | Stationarity along curves of admissible orthogonal transformations. |
| `033000` | Uniform approximation and attainment (`033000-uniform-approximation-and-attainment.md`) | Value convergence, compactness, and distinct optimizer questions. |
| `034000` | The four-dimensional matching reduction (`034000-the-four-dimensional-matching-reduction.md`) | Principal-angle coupling, phases, and reduction to a discrete objective. |
| `035000` | The real matching formula and extensions (`035000-the-real-matching-formula-and-extensions.md`) | Matching values, norm-dependent refinements, and real/complex scope. |


### Unit VII — Beyond finite-dimensional matrices

*Recover the full operator-theoretic problem rather than extrapolating from pictures.*

| Order | Proposed lecture | What the learner should understand |
| --- | --- | --- |
| `036000` | From matrices to Hilbert-space operators (`036000-from-matrices-to-hilbert-space-operators.md`) | Bounded operators, closed subspaces, and dimension defects. |
| `037000` | Spectral measures and functional calculus (`037000-spectral-measures-and-functional-calculus.md`) | Continuous spectrum and projection-valued measures. |
| `038000` | Compact operators and operator ideals (`038000-compact-operators-and-operator-ideals.md`) | Singular sequences, approximation numbers, and symmetric norms. |
| `039000` | Unbounded self-adjoint operators (`039000-unbounded-self-adjoint-operators.md`) | Domains, residual extensions, and valid operator equations. |
| `040000` | The general angle estimates (`040000-the-general-angle-estimates.md`) | Revisit the angle theorem families in the appropriate Hilbert-space settings. |
| `041000` | Completing the 1970 mathematical picture (`041000-completing-the-1970-mathematical-picture.md`) | Source-specific results, exceptional cases, sharpness, and limits of coverage. |


### Unit VIII — Applications to statistical and computational mathematics

*Apply the geometry while tracking exactly what hypotheses transfer.*

| Order | Proposed lecture | What the learner should understand |
| --- | --- | --- |
| `042000` | Rectangular matrices and singular-subspace perturbation (`042000-rectangular-matrices-and-singular-subspace-perturbation.md`) | SVD sensitivity and Wedin-style statements. |
| `043000` | Yu-Wang-Samworth and population eigengaps (`043000-yu-wang-samworth-and-population-eigengaps.md`) | Population-only separation and statistical comparison. |
| `044000` | Eigenframe alignment and Gram rigidity (`044000-eigenframe-alignment-and-gram-rigidity.md`) | Changing bases without changing the represented geometry. |
| `045000` | Classical multidimensional scaling and DKPS (`045000-classical-multidimensional-scaling-and-dkps.md`) | Spectral embeddings from Gram matrices and pairwise data. |
| `046000` | From finite samples to reliable embeddings (`046000-from-finite-samples-to-reliable-embeddings.md`) | Concentration, perturbation propagation, and consistency. |
| `047000` | Downstream inference and query-efficient prediction (`047000-downstream-inference-and-query-efficient-prediction.md`) | What spectral accuracy guarantees for downstream procedures; Helm/Quench as case studies. |


## Learning milestones (draft)

- **Unit I:** Explain why tiny perturbations can swap a selected eigenvector
  when its eigenvalue has little separation from the rest.
- **Unit II:** Compute and interpret projections and principal angles, and
  recognize when basis vectors are not the invariant objects of interest.
- **Unit III:** Derive a simple residual-over-gap estimate and know why the
  theorem hypotheses determine which gap is relevant.
- **Unit IV:** Understand the canonical rotation of subspaces and the
  restrictions under which its construction is defined or distinguished.
- **Unit V:** Select among sine, tangent, and double-angle conclusions by
  checking spectral, structural, and norm hypotheses rather than matching a
  formula by appearance.
- **Unit VI:** Distinguish restricted from whole-space optimality; understand
  the Proposition 4.4 counterexample and the route to matching.
- **Unit VII:** Identify what changes for continuous spectrum, operator
  domains, infinite dimension, and operator ideals.
- **Unit VIII:** Track a spectral error guarantee through subspace alignment
  and a statistical or computational downstream task.

## Prerequisite policy

The course has a **main narrative** and a few **on-demand mathematical
refreshers**; do not require a general-audience listener to complete a full
linear algebra review before the opening problem becomes compelling. The
mathematical toolkit (`002000`) can be consulted as needed. Each later lecture
should recap the specific prerequisites it uses, without re-proving every
previous result. The proposed order follows human comprehension, **not** Lean
imports or the 1970 paper's table of contents. Formal proof dependencies and
historical influence are separate maps.

The direct-rotation unit precedes the full double-angle proofs intentionally:
it supplies geometric language for those proofs. The finite-dimensional
angle-theorem development precedes the Hilbert-space treatment, but the latter
is necessary for source coverage rather than optional decoration. The matching
material follows the geometry and perturbation theory, although its logical
proof dependencies should not be misrepresented as consequences of sine theta.

## Source coverage and existing material

Reuse the **existing**, maintained paper-result inventory for formal coverage;
do not invent a second theorem census or assume a lecture title means a theorem
has been covered in full generality. These links are *editorial source anchors*,
not a claim that current transcripts are ready to reuse verbatim:

| New units | Existing lecture topics to consult | Coverage needing development / checking |
| --- | --- | --- |
| I–II | `basics`, `projections`, `invariant_blocks`, `complementary_projection`, `singular_norms`, `principal_angles`, `polar` | A compelling opening, full two-subspace geometry, relation of frames to spaces. |
| III | `minmax`, `rayleigh_ritz`, `sylvester` | Explicit spectral-gap intuition and careful norm-dependent Sylvester estimates. |
| IV | `matrix_exponential`, `polar`, `principal_angles` | Direct rotation, selection conditions, and exceptional cases. |
| V | `sine_theta` | Tangent, sine-two-theta, tangent-two-theta, and hypothesis comparison. |
| VI | `trace_gradients`, `variations`, `uniform_minima`, `matching_study`, `matching_proof` | Rotation extremality, printed Proposition 4.4 correction, supported real matching claims; compact matching talk remains reference material. |
| VII | `pvm`, `sine_theta` | Domains, operator ideals, general-angle theorems, and unaddressed 1970 results. |
| VIII | `yws` | Rectangular variants, MDS and embedding links, Helm/Quench application chain. |

Source-of-truth starting points in the repository:

- `visualizations/docs/planning/lecture-project-vision-and-history.md`
  (the north star and the distinct learning/formal/history maps).
- `visualizations/LECTURE_STYLE_RULES.md` (direct listener feedback;
  continue to respect it without copying its full text here).
- `visualizations/lectures/index.yaml` (existing registered lecture IDs;
  **do not modify in this draft phase**).
- `dev/davis-kahan-1970-formalization-result-inventory.json` and
  `prose/distilled_literature/DavisKahan1970_part_III.tex`
  (paper-scope correspondence and source reconstruction).
- `dev/yu-wang-samworth-2015-full-source-census.md` and the project
  application semantic reviews for the later units.

## Outstanding design decisions

1. Split or merge difficult lessons after evaluating the spoken drafts, not
   just to match the first table's length.
2. Decide whether some formal proof details are better delivered as separate
   deep-dive episodes or optional written companions.
3. Decide how to attach nonspoken equations, source citations, visual anchors,
   and exercises without putting production metadata into narration.
4. Review theorem and application scope against the maintained source maps as
   each relevant transcript matures.

**First artifact:** `tts-lectures/000000-course-introduction.md` is an
independent narration draft. No Manim design or TTS production claims are made
for it in this stage.
