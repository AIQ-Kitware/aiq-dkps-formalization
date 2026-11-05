# Lecture project: vision, learning map, and mathematical history

Planning draft, 5 November 2026. Authored by GPT-6.1-Sol from Jon's direction.
This is a content plan; proposed lectures below are not yet registered or rendered.

## North star

Build a collection of small, connected lectures through which a learner can
understand the entire Davis–Kahan paper, the extensions developed in this
repository, and the prerequisites needed to explain them. The goal is human
understanding: a learner should eventually be able to state the assumptions,
explain the constructions, and reproduce the important reasoning without an
assistant present. Lean 4 supplies precise mathematical statements and proof
dependencies against which we can validate that learning map.

The collection combines Manim visualizations, standalone transcripts suitable
for TTS, symbolic statements, readable Lean companions, and study questions.
It should support both a guided course and a viewer arriving at one concept
through a search or a link. The repository remains the source of truth; Git
records the evolution of authored material.

We do not need the exact Lean correspondence or dependency tree before making
useful lectures. Scaffold the obvious prerequisites, motivating questions,
geometric explanations, and historical orientation now. Refine their scope
and connections as we inspect the actual proofs. An unfinished formal map is
not a reason to postpone teaching material we already know is useful.

## Three maps that serve different purposes

| Map | What an edge means | Evidence and current home |
| --- | --- | --- |
| Learning prerequisites | Understanding one topic helps a viewer learn another. | Authored teaching judgment in `lectures/index.yaml`; improve it through viewer feedback. |
| Formal proof dependencies | A particular Lean declaration uses another declaration, with particular hypotheses. | Actual pinned Lean sources and compiled declarations; refine the correspondence as each proof lecture is reviewed. |
| Historical development | A publication develops an idea, cites an earlier result, or documents an influence. | Original publications and explicit historical evidence, with dates and locators. |

These maps overlap but need not have the same order. A historical overview can
introduce a mathematician before the learner can prove that person's theorem.
A good lesson may explain a proof differently from Lean's implementation. An
import is not evidence of historical influence, and a publication date alone
does not establish influence or priority.

Use the existing YAML index, numbered lecture folders, provenance files, and
source censuses. Do not create another theorem inventory or require a new
mapping tool before drafting lectures. In each future proof lecture's source
notes, record its exact theorem anchors when known, scope differences, and
unresolved correspondence. A conceptual draft can say that this alignment is
pending without pretending that its mathematical claim has been certified.

## Scope of the eventual course

| Strand | Material to explain | Starting point |
| --- | --- | --- |
| Orientation | Mathematics refresher, historical overview, and how to choose a route through the course. | Existing `000010` basics; history proposed below. |
| Geometry and linear algebra | Subspaces, projections and `I-P`, principal angles, singular values, norms, polar decomposition, and direct rotations. | Existing projections, complementary-projection, singular-norms, and polar lectures; add missing conceptual bridges. |
| Analysis and perturbation | Rayleigh quotients and min–max, spectral separation, residuals, Sylvester equations, functional calculus, operator ideals, and domain-aware unbounded operators. | Existing min–max and Sylvester lectures; infinite-dimensional material needs its own careful introductions. |
| Davis–Kahan | The sine, tangent, double-angle families, their different gap hypotheses and selection issues, and the other established results of the 1970 paper. | Existing sine-theta lecture; plan the remaining source results against the maintained inventory. |
| Correction and transport | Printed Proposition 4.4, its counterexample, the Q-norm repair, real matching reduction and attainment, and the real/complex distinctions and further proved extensions. | Existing counterexample and matching presentations; inspect current theorem scope before extending coverage. |
| Statistical use | YWS population-gap bounds, basis alignment, singular-subspace variants, and a short downstream DKPS/Quench application. | Source reconstruction and semantic reviews, rather than a new application claim. |
| Formal mathematics | How symbolic facts correspond to Lean, what a checked theorem guarantees, and the provenance of reused Mathlib/TauCeti foundations. | Relevant companions within concept lectures; a separate project-history episode can explain the development process. |

The full 1970 source scope includes infinite-dimensional and unbounded settings;
a finite matrix course alone does not fulfill this north star. Teach finite
pictures first where helpful, then identify exactly what changes with domains,
continuous spectrum, and operator ideals. Do not suggest that a numerical
animation proves the general result.

Two routes through shared modules are useful: a patient learner's route with
prerequisite links and expanded justifications, and a compact specialist route
that assumes the stated background. Avoid duplicating every concept in both.
History is an accessible entry point, not a required technical prerequisite for
all later lectures.

## History sequence

Start with an overview that introduces the people, the problems they were
addressing, and the publications in which the relevant work appeared. Follow
with focused episodes that revisit the same history from different mathematical
angles. Target lengths below are editorial estimates, not fixed constraints.
Stable IDs are proposals; use the existing ordering machinery when implementing
them rather than assigning or moving numbered directories now.

| Proposed ID | Working title | Audience and approximate length | Distinct purpose |
| --- | --- | --- | --- |
| `history_overview` | How eigenvector stability became a subject | Refresher-level audience; 15–20 minutes | Introduce the cast and show how geometry, operator theory, numerical analysis, and statistics meet. Draft this first. |
| `history_geometry` | How to compare two subspaces | Basic inner products; 12–18 minutes | Follow principal angles, two projections, and direct rotations across finite and Hilbert-space settings. |
| `history_perturbation` | From approximate eigenvectors to reliable subspaces | Basic eigenvectors; 15–20 minutes | Follow variational approximation, spectral separation, operator equations, and the Davis–Kahan program. |
| `history_statistics` | From numerical error to statistical uncertainty | Basic eigenvectors and covariance intuition; 12–18 minutes | Explain why population-gap bounds matter, with YWS as the central episode and Quench as a short coda. |
| `history_costs` | Measuring movement: from matrix norms to matching | Basic singular values; 12–18 minutes | A later companion on von Neumann, Schatten, Ky Fan, and the separate combinatorial history behind matching. |
| `history_verified_extensions` | Revisiting a classical paper with formal proofs | Familiarity with subspace angles; 10–15 minutes | Tell this project's documented path from formalization to source correction and transport questions, without declaring unresolved priority. |

The overview should stand alone. The focused episodes should also stand alone;
recall the small amount of shared context needed rather than requiring viewers
to remember a name or symbol from another video.

### First draft: overview storyboard

The organizing question is: **When a matrix changes, which features can we still
trust?** Keep a small evolving diagram of a matrix, its eigenvalues, and a
selected subspace. Return to it as each historical contribution adds a way to
ask or answer the question. A readable timeline gives orientation, but does not
replace the mathematical story.

| Beat | People and publication anchors | What the viewer should take away / visual idea |
| --- | --- | --- |
| 1. Title and question | No historical claim needed. | Briefly speak the main concept; show a matrix changing and a selected line turning. |
| 2. Geometry needs more than one angle | Camille Jordan, 1875, *Essai sur la géométrie à n dimensions*. | Comparing higher-dimensional subspaces requires more structure than comparing two vectors. Animate two principal planes; name principal angles without proving their construction. |
| 3. Approximating an eigenproblem | Rayleigh, *The Theory of Sound* (1877); Walter Ritz, 1909. | An approximate vector produces an approximate eigenvalue; the remaining error raises a certification question. Use a vibrating-mode picture and a trial subspace. Reserve precise priority questions for source review. |
| 4. Eigenvalues and eigenvectors ask different questions | Hermann Weyl, 1912; Richard Courant and Ernst Fischer as min–max attribution leads to verify. | Stable eigenvalues do not by themselves identify stable individual eigenvectors near a collision. Show a cluster and its whole subspace remaining meaningful. Do not attach an unchecked date to Courant–Fischer. |
| 5. Hilbert-space geometry and operator equations | Béla Sz.-Nagy, 1947; Marvin Rosenblum, 1956; Chandler Davis, 1958; Tosio Kato, 1966; Paul Halmos, 1969. | Introduce the people behind moving projections, separating subspaces, and solving operator equations. Give each a short problem-and-contribution card; defer technical details to the focused episodes. |
| 6. The Davis–Kahan collaboration | Davis's Parts I (1963) and II (1965); Davis and William Kahan's announcement (1969) and Part III (1970). | The 1970 work brings precise subspace rotation bounds into focus. Animate residual, separation, and angle; mention that the paper contains several theorem families with different assumptions. |
| 7. A numerical and singular-value continuation | Per-Åke Wedin, 1972; Åke Björck and Gene Golub, 1973. | Perturbing singular subspaces and computing subspace angles are related, distinct problems. Label these as later developments, without asserting unverified direct influence. |
| 8. A statistical question changes the useful hypothesis | Yi Yu, Tengyao Wang, Richard Samworth; 2014 preprint / 2015 journal article. | Population quantities and estimates play different roles. Explain why a gap defined using population eigenvalues is useful when the estimate is random. |
| 9. One application, briefly | Hayden Helm, Ben Johnson, Carey Priebe, 2026, *Query-efficient model evaluation using cached responses*. | Spend about 30–60 seconds on Quench: cached responses give a geometry of models that helps predict benchmark performance. Sketch the intermediate embedding/stability steps; do not draw an unexplained direct arrow from DK to query efficiency. |
| 10. The story continues | Briefly name von Neumann, Schatten, and Ky Fan as matrix-norm background; introduce this repository's formalization, source correction, and transport extensions. | Split the map into statistical applications and transport questions. Explain that checking classical mathematics can expose a new question; the matching result is not an improved YWS bound. |
| 11. Summary and study questions | Revisit the same timeline and people cards. | Summarize the contributions by problem, then ask two or three multiple-choice questions about the conceptual relationships rather than birth dates. Offer links to technical lectures. |

Each person should be introduced by full name, the question addressed, a short
plain-language account of the relevant contribution, and a publication card
with title, date, venue, and a source link. Portraits are optional; use them only
with known identity and usable rights. Do not invent conversations, motives,
collaborations, quotations, or biographical anecdotes to make the story lively.
“When and where” means publication evidence first; institutional or geographical
details can be added when independently sourced and useful.

### Focused episode outlines

**Geometry.** Begin with the ambiguity of choosing bases for the same subspace.
Follow Jordan's finite-dimensional geometry, Hotelling's 1936 canonical
correlation perspective, and the Hilbert-space work of Sz.-Nagy, Jacques Dixmier,
Davis, and Halmos. End by connecting two-projection blocks to direct rotations
and to the geometry used in the transport lectures. Hotelling's contribution
is a parallel statistical viewpoint, not an automatic claim of proof descent.
Use later surveys to find primary passages, then cite those passages.

**Perturbation.** Begin with an approximate eigenvector and its residual. Revisit
Rayleigh and Ritz, introduce min–max and eigenvalue stability, then Rosenblum's
operator equation and Kato's operator-theoretic setting. Make Davis's earlier
papers and the Davis–Kahan collaboration the center of the episode. Close with
Wedin and the distinction between theorem bounds and numerical methods. Briefly
show why domains enter the unbounded setting, without turning the history
lecture into a functional-analysis prerequisite.

**Statistics.** Begin with estimating a covariance eigenspace from data. Explain
population versus sample before using those words as shorthand. Build toward
YWS's change in the separation hypothesis, its alignment conclusion, and its
singular-subspace extension. A short later-development pointer can introduce
rowwise errors, for example Cape–Tang–Priebe (2019), with its source checked
before scripting. End with the brief Quench example and the intervening DKPS /
embedding work. Distinguish subspace error, aligned coordinate error, and
prediction error; they require different arguments.

**Measuring movement (later companion).** Begin with two motions that rank
differently under different costs. Introduce John von Neumann's matrix-norm
work, Robert Schatten's operator-space framework, and Ky Fan's eigenvalue-sum
inequalities. End with the separate combinatorial strand represented by Jack
Edmonds: why recognizing a matching problem connects a continuous optimization
question to established discrete algorithms. This is an explanatory connection,
not a claim that Edmonds studied this transport objective. Distinguish
cardinality and weighted matching sources before crediting an algorithm. The
Lean matching-value theorem does not certify an executable blossom algorithm.

**Verified extensions.** Begin with the question “What is the cheapest way to
move one subspace onto another?” Introduce the classical direct-rotation
literature before explaining the printed Proposition 4.4 failure, the supported
repair, and the unrestricted real matching question. Separate the original
mathematics, its later formalization, and possible new extensions. Check the
current transport statements and literature comparisons before making novelty
claims. Include real versus complex scope. End with what Lean checked and what
still requires human source interpretation and explanation.

History episodes need summaries and study questions, but do not need an
artificial Lean listing for a historical fact. Link to the concept lecture's
symbolic/Lean companion where useful. Do not claim Lean verifies an attribution
or establishes who first discovered a theorem.

## Source anchors and unresolved historical work

Start from the checked-in [manuscript bibliography](../../../papers/dk_formalization_journal/references.bib)
and its primary references. The following are concrete publication anchors,
not a claim that every historical passage has already been audited for these
lectures. Links identify the editions to consult; exact contribution/priority
claims need page or theorem locators during transcript drafting.

| Anchor | Publication and source | Use / remaining review |
| --- | --- | --- |
| Jordan | *Bulletin de la Société Mathématique de France* 3 (1875), 103–174; [original digitization](https://www.numdam.org/item/BSMF_1875__3__103_2/). | Principal-angle history; locate the relevant construction in the original notation. |
| Rayleigh and Ritz | *The Theory of Sound*, vol. 1 (1877); Ritz, *J. reine angew. Math.* 135 (1909), 1–61, [DOI](https://doi.org/10.1515/crll.1909.135.1). | Variational approximation; avoid treating the modern compound name as a priority proof. |
| Weyl; Courant–Fischer | Weyl, *Math. Ann.* 71 (1912), 441–479, [DOI](https://doi.org/10.1007/BF01456804). | Check the exact inequality passage; find and verify Courant/Fischer originals before dating their contributions. Formal-proof provenance in TauCeti is a separate matter. |
| Hotelling | *Biometrika* 28 (1936), 321–377, [DOI](https://doi.org/10.1093/biomet/28.3-4.321). | Canonical correlations; verify the precise relation being illustrated. |
| Sz.-Nagy and Dixmier | *Comment. Math. Helv.* 19 (1947), 347–366; *Revue Scientifique* 86 (1948), 387–399; full titles in the bibliography. | Inspect original scope before attributing a particular projection/rotation construction. |
| Rosenblum | *Duke Math. J.* 23 (1956), 263–269, [DOI](https://doi.org/10.1215/S0012-7094-56-02324-9). | Operator equation; do not credit every modern gap estimate to the same theorem. |
| Davis and Kato | Davis, *Acta Sci. Math. (Szeged)* 19 (1958), 172–187, [original PDF](https://acta.bibl.u-szeged.hu/13858/1/math_019_fasc_003_004_172-187.pdf); Kato, *Perturbation Theory for Linear Operators*, first edition (Springer, 1966). | Subspace separation and operator perturbation context; distinguish first edition from the 1976 second edition. |
| Halmos | *Two Subspaces*, *Trans. AMS* 144 (1969), 381–389, [DOI](https://doi.org/10.1090/S0002-9947-1969-0251519-5). | Two-projection structure; do not attribute Jordan's earlier finite geometry solely to Halmos. |
| Davis–Kahan | Announcement, *Bull. AMS* 75 (1969), 863–868, [DOI](https://doi.org/10.1090/S0002-9904-1969-12330-X); Part III, *SIAM J. Numer. Anal.* 7 (1970), 1–46, [publisher](https://epubs.siam.org/doi/abs/10.1137/0707001). | Earlier Davis papers and exact source scope remain visible; use the source reconstruction and result inventory. |
| Wedin; Björck–Golub | *BIT* 12 (1972), 99–111, [DOI](https://doi.org/10.1007/BF01932678); *Math. Comp.* 27 (1973), 579–594, [DOI](https://doi.org/10.1090/S0025-5718-1973-0348991-3). | Distinguish singular-subspace perturbation from computing angles. |
| Matrix costs and matching | von Neumann, *Some Matrix-Inequalities and Metrization of Matric-Space* (1937); Schatten, *A Theory of Cross-Spaces* (Princeton, 1950); Ky Fan, *PNAS* 37 (1951), 760–766, [original article](https://pmc.ncbi.nlm.nih.gov/articles/PMC1063464/); Edmonds, *Paths, Trees, and Flowers*, *Canad. J. Math.* 17 (1965), 449–467, [original paper](https://web.eecs.umich.edu/~pettie/matching/Edmonds-paths-trees-flowers.pdf). | Norm attribution and the combinatorial continuation; precise weighted-algorithm attribution remains to be checked separately. |
| Yu–Wang–Samworth | [2014 preprint](https://arxiv.org/abs/1405.0680); *Biometrika* 102 (2015), 315–323, [journal DOI](https://doi.org/10.1093/biomet/asv008). | Population-gap variant and rectangular extension. Use published numbering and the repository's source reconstruction. |
| Quench | Helm, Johnson, Priebe, ICML 2026, PMLR 306, 42691–42706, [publication](https://proceedings.mlr.press/v306/helm26a.html). | Brief application only; consult the application semantic reviews before describing the precise theorem chain. |

Publication metadata for Jordan, the YWS preprint, and Quench was checked against
the linked primary publication records while preparing this plan. Remaining
entries start from the repository bibliography; inclusion here does not mean
their original texts or historical priority have been freshly audited.

Useful local evidence:

- [Davis–Kahan source reconstruction](../../../prose/distilled_literature/DavisKahan1970_part_III.tex)
  and [29-result inventory](../../../dev/davis-kahan-1970-formalization-result-inventory.json).
- [YWS source reconstruction](../../../prose/distilled_literature/YuWangSamworth2015_statistical_davis_kahan.tex)
  and [source census](../../../dev/yu-wang-samworth-2015-full-source-census.md).
- [Application semantic review](../../../dev/dkps-application-result-semantic-review.md)
  and [Quench semantic review](../../../dev/quench-2026-result-semantic-review.md).
- [Publication direction](../../../dev/publication-direction-dkps-to-transport-2026-10-27.md)
  and [transport provenance comparisons](../../../dev/spectral-transport-unification.md).
- [DKPS-to-TauCeti contribution ledger](../../../dev/tauceti/dkps-upstream-contribution-census.md):
  distinguish adapted proofs, roadmap origins, independent implementations,
  and earlier Spectra ancestry. A TauCeti namespace does not establish authorship.

## Practical build order

1. Draft the overview transcript and publication cards. Review the historical
   claims and people-to-contribution links before spending time on animations.
2. Build the overview's shared timeline and a few recurring geometric scenes.
   Keep the people and their problems central; detailed proofs belong elsewhere.
   Add title/model provenance, a summary, and conceptual study questions.
3. Register the completed draft through the existing YAML/deck system, let the
   numbering tool place it, render, and inspect its narration and visuals.
4. Draft geometry and perturbation episodes using the same source notes, then
   the YWS-focused statistical episode and the project-history episode. Adjust
   the split if a single episode becomes a list of names rather than a story.
5. Continue filling the obvious technical prerequisite gaps while progressively
   checking each proof lecture against exact Lean declarations and hypotheses.
   Use that correspondence to discover missing lessons, not to postpone all
   lessons until a complete formal dependency graph exists.

A useful first milestone is one standalone historical overview in which a
viewer can explain who addressed which problem, find the cited publications,
and choose the next concept to study. The eventual milestone is a coherent
route through the entire source paper and this project's extensions, with
formal correspondence precise enough to expose missing assumptions or missing
teaching steps.
