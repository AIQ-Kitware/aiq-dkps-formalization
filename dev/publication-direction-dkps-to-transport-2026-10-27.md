# Publication direction: the Davis--Kahan formalization enabled spectral-transport research

**Research steering note -- 27 October 2026.** Read this at the start of the next publication-directed proof checkpoint, together with [the current mathematical research plan](schatten-transport-research-plan.md), [the publication-core assessment](spectral-transport-publication-core.md), [the source-level unification/provenance map](spectral-transport-unification.md), [the original paper result inventory](davis-kahan-1970-formalization-result-inventory.json), and [the DKPS-to-TauCeti contribution census](tauceti/dkps-upstream-contribution-census.md). The current mathematical statements in those records remain authoritative; this note changes **research priorities and publication framing**, not theorem status.

## The story we are trying to establish

**The Davis--Kahan formalization effort was an enabling *research and software-infrastructure prerequisite* for the subsequent formally verified spectral-transport program.** It is not claimed that the sine-theta theorem logically implies the matching theorem, or that formalizing all of Davis--Kahan was mathematically necessary to exhibit a small counterexample. A mathematician could in principle derive these finite-dimensional results by other methods. Our factual claim is about the path and the reusable formal foundations of *this* research program.

The defensible chain is:

1. **Foundations and source fidelity.** Formalizing the 1970 paper required substantial work on Hilbert-space/operator theory, projections, principal angles, direct rotations, operator ideals, and unbounded-operator/spectral results. The maintained inventory records **29 reviewed source targets: 28 proved at reviewed source scope, and the printed Proposition 4.4 refuted**. Source semantic alignment was separately reviewed; a Lean build does not by itself prove that an informal statement was transcribed correctly.
2. **Upstream contribution and reuse.** Parts of that formalization effort became accepted TauCeti operator-theory infrastructure, replacing local donor files. Thus a `TauCeti.*` import in the new research may itself descend from DKPS. Conversely, some overlapping TauCeti developments were independently proved, and some donor mathematics had earlier ancestry (notably Spectra). Do not infer origin from an import path or a roadmap topic alone.
3. **A mathematical discrepancy.** Auditing Section 4 exposed a counterexample to the printed real direct-rotation optimality claim in Proposition 4.4. The small-real-angle failure starts with two principal planes in real four-dimensional ambient space; its mechanism is related to the *already-known* complex phase construction in Davis--Kahan. Do not claim the phase mechanism was first discovered here.
4. **A new optimization question.** The source claim asks whether direct rotation minimizes the displacement of a transporting orthogonal/unitary map for a given unitarily invariant norm. Following that precise objective led to an exact finite-dimensional **real** reduction: for `1 <= p < 2`, the unrestricted Schatten-power minimum over all ambient orthogonal transporters is attained and equals a weighted matching minimum on the labelled positive principal angles. The nuclear endpoint gives explicit singleton and pair weights. This is not merely an optimization restricted in advance to independent principal planes.
5. **Consequences and further theory.** The nuclear matching theorem supplies the sharp real canonical-*value* criterion and the even-multiplicity criterion for equality with the complex minimum. The separate complex smoothed-power/phase-transition/ideal theory is also formally established, with scope recorded in the current publication-core assessment. The new work is motivated by, and reuses infrastructure from, the Davis--Kahan effort; it should not be marketed as an improved sine-theta perturbation bound absent such a theorem.

The claim **"formalization enabled discoveries"** needs these separate pieces of evidence: chronology, source-fidelity record, accepted donor lineage, direct proof dependencies, and a mathematical explanation of the discovered problem. Mere import counts or the number of generated Lean theorems do not establish causation, necessity, originality, or mathematical significance.

## Publication hypothesis, deliberately adversarial

A plausible paper for *Research in the Mathematical Sciences* is a focused account of **formalizing Davis--Kahan and using that verified infrastructure to detect, correct, and investigate a failure of direct-rotation optimality**, with the unrestricted real matching theorem as the clearest candidate for additional original mathematics.

That is a **publication hypothesis**, not an editorial acceptance prediction. The existing larger complex transport theory may merit a separate mathematical article. Do not make the 70-page accumulation of all results the default paper just because the Lean results compile.

Two distinct claims need different defenses:

- **Formalization contribution:** exact reviewed scope of the 1970 text; discrepancy/correction; reusable operator-theory formalizations (including accepted upstream descendants); reproducibility and proof provenance. Its value is not measured by the number of newly invented theorems. An exact small matrix refutation might be independently formalizable without the full library; acknowledge this and document which foundations this research *actually used*.
- **Original-mathematics contribution:** a theorem solving unrestricted real transport by matching, plus explicit weights, attainment and field-dependent consequences. The global **lower bound against all ambient orthogonal transformations** is the nontrivial claim to expose; a construction for each matching only provides the upper bound. Novelty remains conditional on specialist scrutiny of prior art.

Do not conflate proof kernel acceptance with explanation or priority. A successful formal proof establishes its Lean proposition, not a compelling mathematical article or the original authors' priority. A referee should be able to read conventional statements, see a proof mechanism, reproduce a small example, and understand what is different from the nearest published result.

## Concrete mathematical nucleus: real matching

Let `K,L` be equal-dimensional real subspaces of a finite-dimensional Euclidean space, with **labelled strictly positive** principal angles `theta_1,...,theta_k` (repetitions remain separate labels). Define

\[
D_{p}(K,L) = \min_{U \in O(n),\,U(K)=L} \|I-U\|_{S_p}^p, \qquad 1\le p<2.
\]

The current Lean development establishes an attained global matching formula throughout this exponent range. At **p=1**, with unmatched and paired costs

\[
s(\theta)=\min\{4\sin(\theta/2),2\}, \qquad
 e(\theta,\psi)=4\sin((\theta+\psi)/2),
\]

the minimum is the cost of a matching of positive angle labels, counting singleton costs for all unmatched vertices. A maximum-weight **general-graph** matching with edge savings `s_i+s_j-e_ij` computes the same value. That is **not** ordinary bipartite Hungarian/Munkres assignment. The Lean theorem establishes value/attainment, not a verified executable blossom algorithm or numerical stability guarantee.

The two-angle `theta_1=theta_2=pi/6` example is a minimum reproducible witness:

\[
\text{direct rotation: }8\sin(\pi/12)\approx2.070552,
\qquad
\text{paired real transporter: }4\sin(\pi/6)=2.
\]

Existing source anchors (check exact namespaces/statements before quoting):

- `DavisKahan/FiniteDimensional/DirectRotation/RealNuclearMatching.lean`: `RealNuclearMatching.exists_minimizing_real_schatten_transport_matching_of_one_le` and `exists_minimizing_real_nuclear_transport_matching`.
- `DavisKahan/FiniteDimensional/DirectRotation/RealNuclearExchange.lean`: `realNuclearPairWeight_submodular` and `realNuclearPairWeight_adjacent_exchange`.
- `DavisKahan/FiniteDimensional/DirectRotation/RealNuclearFieldEquality.lean`, `RealNuclearOptimality.lean`: nuclear real--complex equality and canonical-value criteria.
- `DavisKahan/FiniteDimensional/DirectRotation/SmallAngleCounterexample.lean`, `QNorm.lean`: source correction and repaired classical norm regime.
- `DavisKahan/FiniteDimensional/DirectRotation/SmoothedPowerBoundary.lean`, `SmoothedPowerCanonicalCriterion.lean`, `DavisKahan/InfiniteDimensional/DirectRotation/SmoothedPowerGlobalAttainment.lean`: the separate completed complex family results.

**Important open boundary:** the nuclear adjacent-pair exchange inequalities are verified, but the proposed full **two-sorted-sums formula** was not Lean-proved at this checkpoint. Exchange for four sorted angles alone is *not* an induction over arbitrary matchings with unmatched vertices. Treat any `O(k log k)` sorting-only claim as conjectural until the global normalization and recurrence are proved. No result for arbitrary real positive-smoothing penalties or general infinite-rank real matching follows from the finite matching theorem.

## What an adversarial specialist will ask

1. **"Why did the entire Davis--Kahan formalization matter?"** Separate a *minimal mathematical dependency slice* of the counterexample and real matching proof from broader project-created infrastructure. Identify actual statements consumed, which are pure Mathlib/TauCeti, which were directly developed here then upstreamed, and which were independently developed. Do not say all 29 targets were required for the four-dimensional counterexample.
2. **"Was the optimization problem known?"** Yes. Davis (1958), Davis--Kahan (1970), and Bolotnikov--Li--Rodman (2001) already contain essential norm and minimal-distortion mathematics. The contribution cannot be the definition of the transport fiber, the idea of principal angles, or awareness that complex phase modifications can beat direct rotation for nuclear norm.
3. **"Is the real matching theorem actually new?"** Not resolved. Attempt to derive it from exact predecessor theorems, including matrix majorization, quotient Grassmann metrics, real orthogonal canonical forms, and Procrustes formulations with *the same* feasible set and objective. Cite theorem numbers/pages and explicitly distinguish chordal `||I-U||` from geodesic/logarithmic norms. Negative searches are not proof of first priority.
4. **"Where is the hard theorem?"** Give the argument reducing a genuinely unrestricted orthogonal transporter to optimal one-plane/two-plane blocks. Distinguish construction/upper bound from universal lower bound. The scalar pair-weight calculus alone does not answer this question.
5. **"Does matching buy an algorithm?"** Establish what input the algorithm takes (principal angles with multiplicities), how the optimal matching is found (general graph), and how the attaining orthogonal transporter is built from it. Determine whether the sorting simplification is true; if not, preserve matching rather than announcing the faster bound.
6. **"Can a human explain it?"** Provide a conventional proof and a four-dimensional example, followed by at least one example with **three or more distinct positive principal angles** where pairing choices matter. Show why the construction is globally optimal and why changing `p` alters the choice. Avoid an exposition that merely repeats Lean declaration names.
7. **"What is the actual literature correction?"** Cite the *printed* Proposition 4.4 and the exact failed step; preserve the known phase counterexample and the Q-norm repair as prior/context. The reported Aubrun--Szarek (2017) Exercise B.12 conflict is a useful lead but the printed-edition wording is **not independently authenticated** in the archival priority review. Do not publish a precise book correction without checking the authoritative edition.
8. **"Do these results change a downstream DK/QUENCH bound?"** Not yet established. A possible application is not a result. Do not imply the matching theorem improves the sine-theta theorem or QUENCH without a precise proven inequality and its needed noise assumptions.

## Publication-directed agenda for the proving agent

**At the next completed/committed checkpoint**, stop selecting optional goals simply because they are on the research backlog. Retain the proved C1/C2/C5 complex results and the real matching results; do not invalidate or re-prove them for cosmetic narrative reasons. The next proof should improve a referee-facing mathematical claim or reveal that a supposed contribution is already routine.

### Priority 0: establish an independently readable matching proof and dependency ancestry

- Read the global real matching proof and write a *short conventional mathematical proof skeleton* with precise propositions: geometric normal forms, feasible two/four-dimensional constructions, compactness/existence as applicable, **unrestricted lower bound**, and attainment. Name where each step is classical versus newly formalized. If an elementary known matrix inequality already implies the lower bound, record it rather than obscuring it.
- In the same record, construct a **declaration-level ancestry path** (not just transitive module import counts) from the counterexample and matching theorem through DKPS-developed foundations to accepted TauCeti declarations. Reuse `dev/tauceti/dkps-upstream-contribution-census.md`, roadmap intention #776, donor sources/PRs, final accepted APIs, and any Spectra ancestry. Categories must remain: direct adaptation, derived/generalized, campaign-associated, independently developed, and source unknown. If exact accepted-diff inspection isn't possible, say so.
- Identify whether a smaller self-contained formalization could produce Proposition 4.4's counterexample, and say honestly how that affects the "prerequisite" wording. The historical/programmatic dependency is still valid even if logical necessity is false.
- Extract an example that a computer scientist can check numerically or symbolically: calculate the two candidate singular-value spectra and nuclear sums, and demonstrate actual orthogonality/transport for the alternative. Do not replace a verified theorem with numerical evidence.

**Acceptance gate:** another mathematician can read the one-page statement and proof roadmap and identify precisely what would need to be checked to verify global optimality. The evidence record says exactly what grew out of the DKPS formalization rather than attributing all TauCeti imports to it.

### Priority 1: one high-leverage proof target, not another program expansion

Try to finish the **real nuclear sorted-adjacent matching normalization** if it is correct. The scalar four-angle exchange is already proved. The remaining question is whether any arbitrary matching with optional singletons can be normalized into the proposed two sorted patterns, preserving minimum cost. Either:

- Prove the exact sorted-sums statement in Lean, including `k=0/1`, ties, right angles, optional unmatched vertices and the inductive exchange/normalization step; connect it to the existing unrestricted transport minimum; or
- Produce a mathematically explicit counterexample to the two-pattern reduction or an identified obstruction. Do not manufacture an unproved speedup just because it makes a good CS story.

If sorting fails or becomes intractable without new insight, the **verified general-graph matching result is already a complete, computationally meaningful theorem**. Move on to the publication exposition and priority comparison. Do not take up full infinite-dimensional real matching or all-penalty optimizer topology merely to remain busy.

**Acceptance gate:** a new, correctly scoped Lean theorem that makes the algorithmic contribution more precise, or a clear mathematical reason to retain the general matching formulation. Preserve the status of this target as open until compiled.

### Priority 2: challenge the novelty and define the paper boundary

- Prepare theorem-to-theorem comparisons with Davis 1958 (notably 7.3/7.4), Davis--Kahan 1970 Section 4, Bolotnikov--Li--Rodman 2001 Problem 1.1 and theorems/lemma, Qiu--Zhang--Li and Zhang--Qiu. Record **what each source actually proves** and which hypotheses differ. Do not cite later literature as though it was original when an earlier source already contains the idea.
- Examine a possible direct consequence of the newly formalized source perturbation bounds: a transparent bound on *optimal* matching transport from a DK subspace perturbation estimate. If it is only a trivial substitution, label it an expository corollary, not novel mathematics. **Do not require this link to justify the historical project trajectory.**
- Propose one focused paper structure: classical DK formalization and verified discrepancy, provenance and reusable foundations, exact real matching as a bounded follow-on case study, explicit limitations. Provide a second *optional* pure spectral-transport paper plan if the mathematics is too large to communicate responsibly in one article.
- Keep the full complex two-parameter family available, but do **not** turn it into a mandatory condition for the formalization paper. Its priority and significance must be evaluated independently.

**Acceptance gate:** a skeptical reader can distinguish formalization contribution, historical correction, a candidate original theorem, and speculative applications. The scope fits what the author can eventually explain and what an external specialist can referee.

### Deferred unless explicitly authorized

Do not automatically launch campaigns for generic arbitrary spectral penalties, complete all-field/penalty classifications, indefinite infinite-dimensional real matching, exhaustive topology or global stability, or QUENCH concentration rates. These may be valuable, but their contribution to this paper must be stated **before** using them as a reason to extend the codebase.

## Agent deliverables and honest status reporting

Continue mathematical work in Lean where it moves the paper toward a defensible claim. This is **not** a request to stop proving things. It is a change in what proof work gets priority.

For each completed checkpoint, report in a compact note or update to the existing plan (do not create a parallel census or automation system):

1. Exact Lean declarations proved or refuted, and the scope of their hypotheses; compile status using `lake exe cache get` before `lake build`.
2. The mathematical point, in ordinary mathematical language, plus a small worked example when useful.
3. Precise upstream/source provenance; distinguish proof dependence from the historical development path and from priority in the published mathematical literature.
4. Why this result strengthens the publication: necessary for the main argument, a sharper algorithm, an independently useful corollary, a source correction, or a **negative result that narrows the claim**.
5. Remaining questions with their priority, and whether another theorem is justified before conventional exposition and external review.

Respect `AGENTS.md`, the upstream-first policy, the maintained source inventory and the canonical research handoff. Do not add test dashboards or repetitive theorem dumps. Do not edit `papers/`, Manim or submission letters in this phase; the manuscript will be revised after the proof/narrative boundary is settled. Do not contact authors, editors, or make public novelty claims without the user's instruction.

**Stop condition for the present direction:** the matching theorem has an intelligible, source-attributed proof outline, a verified or explicitly refuted sorting improvement, a supported DKPS-to-upstream ancestry diagram, and a clear hostile literature comparison. At that point, recommend writing/reviewing the focused article rather than proving another unrelated theorem. If the sorting direction has no progress, it does **not** block this stop condition: the existing matching theorem is complete.
