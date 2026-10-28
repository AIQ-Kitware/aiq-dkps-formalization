# Supplied historical-priority review — 26 October 2026

## Provenance and scope

**28 October update:** a bounded independent check now authenticates the
reported wording in the authors' preliminary PDF, not in the printed edition.
See the final version-specific update. The supplied review below retains its
original evidence level; do not mistake its older access status for the new
primary-version check.

The user supplied an external agent's **“Historical priority review — October
26, 2026”** in the conversation on this date. This record preserves its
findings, comparisons, negative-search limits and remaining checks so another
agent can resume rather than repeat them. It is an attributed research record,
not an independent verification of its source inspections or a declaration of
historical priority. Favicon links and download UI in the supplied text did not
provide the underlying full research note; that attachment is not archived here.

The existing [novelty review, sections 7–11](../papers/dk_formalization_journal/MATHEMATICAL_NOVELTY_REVIEW_2026-10-24.md)
already records overlapping source inspections, exact source links and an
important limitation: Appendix B was inspected through a third-party textual
reproduction, while the author-hosted Chapter 5 and September 2023 errata were
inspected directly. The new report mentions a Lyon-hosted source but supplies
no full URL, edition identifier or page scan. **Do not silently upgrade this
to authentication of the printed Appendix B.** No author contact is authorized
or recorded by this document.

Mathematical status is separate from priority. The report's statement that
general infinite-rank attainment remains open is superseded for the complex
`1<p<2` theory: native Schatten projection difference and balanced crossed
defects now yield attainment and classification of every optimizer. See the
[current research handoff](schatten-research-handoff-2026-10-26.md) and the
[current research plan](schatten-transport-research-plan.md) for exact hypotheses
and remaining obligations. Complex infinite-rank nuclear and smoothed
optimizer classifications have subsequently been proved as recorded there.
The report below retains its attributed historical-search scope.

## Main reported finding: Aubrun–Szarek Exercise B.12

Source: Guillaume Aubrun and Stanisław J. Szarek, *Alice and Bob Meet Banach:
The Interface of Asymptotic Geometric Analysis and Quantum Information*,
American Mathematical Society, Mathematical Surveys and Monographs 223 (2017).

The supplied review reports that Appendix B defines the extrinsic quotient

\[
 d_p(E,F)=\min_{W\in O(n),\ W(E)=F}\|W-I\|_{S_p},
\]

and that Exercise B.12 asserts independent principal-plane direct rotations
attain this minimum for every `1≤p≤∞`. Its hint reportedly asserts
coordinatewise singular-value domination. This is the same unrestricted
real transporter constraint studied here, rather than a frame-fitting problem.

The review's counterexample has two real 2-planes in `R⁴`, both principal
angles `π/6`. Displacement singular values and nuclear costs are

| Transporter | Displacement singular values | Nuclear cost |
| --- | --- | --- |
| Canonical direct rotation | `(2 sin(π/12), 2 sin(π/12), 2 sin(π/12), 2 sin(π/12))` | `8 sin(π/12) ≈ 2.070552` |
| Realification of complex phase competitor | `(1,1,0,0)` | `2` |

Thus the quoted extrinsic formula and coordinatewise domination fail; the
third and fourth singular values directly contradict the latter. The review
reports independent numerical verification of orthogonality and angles.
That verification is an external report, not new Lean evidence from this
archival change. Existing formal counterexamples and the mathematical source
comparison remain in the linked project records.

The report says the published errata, last updated September 2023, do not
list Exercise B.12. This is a dated observation about the inspected errata,
not a claim about every printing or the current errata. The separate
shortest-geodesic/logarithmic-distance formula is **not** refuted by this
extrinsic counterexample.

Existing source links, retained to avoid a repeated search:

- [Authors' book page](https://case.edu/artsci/math/szarek/ABMB/ABMB.html).
- [Author-hosted Chapter 5, Table 5.1](https://case.edu/artsci/math/szarek/ABMB/ABMBchapter5.pdf).
- [Authors' errata](https://case.edu/artsci/math/szarek/ABMB/errata.pdf).
- [Third-party book-text reproduction; edition unauthenticated](https://dokumen.pub/alice-and-bob-meet-banach-the-interface-of-asymptotic-geometric-analysis-and-quantum-information.html).

## Closest predecessors and exact distinctions reported

1. **Bolotnikov–Li–Rodman (2001), “Minimal Distortion Problems for Classes of
   Unitary Matrices,” Electronic Journal of Linear Algebra 8, 26–46.** Problem
   1.1 already poses the ambient unitary subspace-transport minimum. The report
   identifies complete Frobenius results, Q-norm results covering Schatten
   `p≥2`, and Lemma 3.3's special `1≤p<2` failure. It did not locate arbitrary-
   angle subquadratic global formulas, unrestricted real weighted matching,
   or complete intermediate-exponent optimizer classification in the inspected
   statements. [Official journal PDF](https://journals.uwyo.edu/index.php/ela/article/download/117/117/117).
2. **Davis–Kahan (1970), “The Rotation of Eigenvectors by a Perturbation. III,”
   SIAM Journal on Numerical Analysis 7, 1–46.** The complex phase mechanism
   and trace nonoptimality are already present. The specific real Proposition
   4.4 correction is distinct from discovering that mechanism.
   [Article DOI](https://doi.org/10.1137/0707001).
3. **Qiu–Zhang–Li (2005/2006), “Unitarily Invariant Metrics on the Grassmann
   Space,” SIAM Journal on Matrix Analysis and Applications 27, 507–531.**
   Section 5 reportedly repeats the disputed small-angle optimality assertion.
   Its matrix-logarithm/path-length theorem is a different optimization
   objective and is not refuted here. The report notes volume year 2005 and
   online publication in 2006. [Article DOI](https://doi.org/10.1137/040607605).
4. **Zhang–Qiu (2010), “From Subadditive Inequalities of Singular Values to
   Triangle Inequalities of Canonical Angles,” SIAM Journal on Matrix Analysis
   and Applications 31, 1606–1620.** Explicit recognition of trace-norm
   nonoptimality rules out a novelty claim for nonoptimality alone.
   [Article DOI](https://doi.org/10.1137/09074841X).

These links identify sources already recorded in the repository; this archival
change does not claim a new independent reading of them.

## Supplied theorem-level priority assessment

These judgments belong to the external report, not a proof of first discovery.

| Claim | Supplied assessment |
| --- | --- |
| General transporter minimization problem | Previously studied in 2001 |
| Direct-rotation nuclear nonoptimality | Known in substance since 1970 |
| Proposition 4.4 counterexample at arbitrarily small angles | Specific correction not located earlier; related false claim persists in later sources |
| Complex nuclear minimum `2∑ sin θ_j` | Established here; classical ingredients leave independent priority uncertain |
| Unrestricted real nuclear weighted-matching formula | Strong originality candidate |
| Real–complex nuclear equality iff every strictly acute positive angle has even multiplicity | Strong originality candidate |
| Real canonical-value criterion: at most one positive angle, no larger than sixty degrees | Sharp correction and consequence of matching |
| Complex `1<p<2` phase transitions and complete global optimizer classification | Strong originality candidate |
| No nonglobal complex local minima for intermediate exponents | Strong candidate; related theorems use different feasible domains |
| Exact Charbonnier/smoothed transport optimization | Promising candidate; equivalent transport theorem not located |
| Infinite-dimensional defect-index obstruction | Established index-theoretic background |
| Infinite-dimensional lower bounds and finite-rank attainment | Valuable verified extensions; the report's broader-attainment-open status is superseded as explained above |

## Adjacent formulations already searched

The report says it checked original articles, publicly available manuscripts,
cited references and neighboring terminology, including:

- Orthogonal Procrustes/frame fitting, including Watson: related objectives
  and constraints, but no equivalence to unrestricted subspace transport
  established in this search.
- Grassmannian shortest paths and logarithmic displacement: intrinsic costs
  differ from `‖I-W‖_{S_p}`.
- Massey–Rios–Stojanoff local Lidskii theorems: spectral/singular-value orbit
  local-to-global results; reduction to the transporter fiber not established.
- Andruchow–Larotonda–Recht restricted Schatten-unitary geometry: path lengths
  and orbit geometry, not automatically extrinsic chordal minimization.
- Pairs of projections and relative index: classical feasibility background,
  including Avron–Seiler–Simon; not a new obstruction invented here.
- Loring's real/complex principal-angle structures: projection geometry and
  approximation, without an equivalent matching/parity theorem located.

The earlier supplied review also singled out Contino–Giribet–Maestripieri,
*Weighted Procrustes Problems* (2017), as optimization over weighted bounded-
operator equations with a different feasible set. The cumulative novelty review
has further source details. These are **checked neighborhoods**, not proof
that all papers in them are irrelevant.

## Search limits and precise remaining historical obligations

The external agent did **not** perform exhaustive authenticated MathSciNet or
zbMATH clearance. Citation indexing was unavailable or inconsistent, and some
older full texts were unavailable. Its strongest conclusion was:

> No earlier statement equivalent to our unrestricted real weighted-matching
> theorem, exact nuclear parity criterion, or complete intermediate-exponent
> complex phase-transition classification was located in the primary sources
> examined.

Preserve this limited negative-search conclusion. Do not replace it with
“first theorem” or “no prior work exists.” The next useful historical checks
are:

1. Obtain an authenticated printed/publisher/author Appendix B and verify
   equation, exercise, normalization, hint and edition; check later corrections.
2. Follow BLR and Qiu–Zhang–Li citation chains with authenticated indexing.
3. Compare equivalent block-diagonal approximation, restricted Procrustes and
   quotient-distance formulations theorem by theorem, including feasible sets.
4. Independently review the claimed mathematical endpoints against their actual
   Lean hypotheses. Source priority and compiler verification are separate.

The report suggests considering a scholarly correction after primary-edition
verification and author communication. This is a recommendation for future
human review, not an action taken or authorized here.

## Publication recommendations supplied, not manuscript edits

The external report recommends centering exact optimization theory: the real
matching theorem and parity criterion, complex phase transitions and optimizer
classification, with the historical correction as supporting context. It
proposes describing the work as extending earlier minimal-distortion results
beyond their classical Frobenius/Q-norm regimes, rather than inventing the
optimization problem or the phase mechanism. Infinite-dimensional claims must
use the current handoff, not this report's superseded snapshot.

No manuscript or visualization is changed by this archive. The paper's framing,
precise novelty wording and any correspondence remain separate work.


## Independent version-specific update — 28 October 2026

The [author-hosted preliminary PDF](https://math.univ-lyon1.fr/~aubrun/ABMB/ABMB.pdf)
was directly inspected at (B.13), p. 316; Exercise B.12, p. 317; hint, p. 371.
It confirms the reported formula and domination assertion in that version.
The authors' page labels the file preliminary; publisher access returned 403.
The printed edition therefore remains unauthenticated. The exact transport
comparison and newly proved nuclear sorting theorem are recorded in the
maintained unification note, sources S10/S14/S15 and provenance T21/T22.
No author contact was made.
