# Overnight plan: make real spectral transport referee-ready

Prepared 27 October 2026. **Execution activated by the user, 28 October 2026.**
The conventional lower-bound roadmap and complete nuclear sorting/ambient
attainment theorem are proved and documented. The 21,507-job full build
passed. Worked examples and targeted primary-source comparison remain active;
then the final handoff will audit every outcome below.

This plan follows the publication direction in
[the steering note](publication-direction-dkps-to-transport-2026-10-27.md),
with the user's subsequent correction: **do not spend the night reconstructing
DKPS-to-TauCeti ancestry.** That evidence is already maintained in another
repository. Preserve existing attribution and consult it only if a particular
proof or priority claim needs clarification. Do not create a new ancestry
inventory, inspect integration history exhaustively, or edit that other repo.

## Outcome sought

Strengthen the focused contribution: the Davis--Kahan source discrepancy led
to an exact unrestricted real transport problem, whose attained solution is
weighted matching on labelled principal angles. By morning we should have:

1. A short conventional explanation of the universal lower bound and attainment,
   with its precise Lean anchors and classical versus potentially new steps.
2. A compiled nuclear sorting theorem connected to the ambient minimum, or an
   explicit, mathematically informative disposition of the proposed reduction.
3. Worked examples and a skeptical comparison with the closest published
   theorems, sufficient to sharpen the paper's contribution boundary.
4. Green committed mathematical checkpoints and an honest final handoff.

The already proved general matching theorem remains a complete result if
sorting fails or its formal proof remains unfinished. The completed complex
family theory is preserved; expanding it is outside this run.

## Sequence and effort allocation

Use roughly a six-to-eight-hour working window if needed. These are allocation
estimates, not promises about theorem difficulty. Work sequentially with one
agent on main. Finish early if the outcomes are achieved; do not fill remaining
time with unrelated theorems. Reserve the final hour for integration and handoff.

### 1. Expose the unrestricted proof mechanism — about 45–60 minutes

Read the actual strict-exponent reduction, not just the matching construction:

- `SchattenRealDecomposition.lean`:
  `exists_complete_real_blocks_of_isLocalMinOn_real_transports`.
- `SchattenRealRestrictions.lean`:
  `exists_complete_globally_minimizing_blocks_real`.
- `SchattenRealMatching.lean`, `SchattenRealMatchingWeights.lean`:
  `exists_matching_cost_eq_of_isMinOn_real_transport` and
  `realPositiveSchattenMatchingMinimum_le_of_map_eq`.
- `RealMatchingAttainment.lean`:
  `exists_real_transport_attaining_matching` and
  `exists_minimizing_real_schatten_transport_matching`.
- `RealNuclearMatching.lean`: compact continuation to p=1 and actual attainment.

All are under `DavisKahan/FiniteDimensional/DirectRotation/`, with namespace
`TauCeti.DavisKahan.FiniteDimensional.RealTransport`.

Write a one-page mathematical proof roadmap in the existing unification note,
with further details only where they explain a hard step. It must explain:

1. Compactness gives a global minimizer on the full orthogonal transport fiber.
2. Its real-constrained stationarity, spectral restrictions and descent yield
   complete real reducing sectors of dimension at most four, retaining the
   zero-gradient sector and real conjugation constraints.
3. Every restriction is itself an unrestricted **real** minimum, by feasible
   block replacement. Costs add, and angle multisets assemble with labels and
   multiplicities intact.
4. Exact two/four-dimensional costs turn that global minimizer into a matching.
   This gives the lower bound against every ambient competitor.
5. Conversely, every matching is realized by an actual ambient transporter.
6. Compact value continuity extends the strict range to the nuclear endpoint;
   this is not an unsupported nuclear differentiability argument.

Do not say that every arbitrary transporter already has the minimizing block
structure, or that real local minima are global. Do not present the upper-bound
construction as the universal lower-bound proof. Flag any genuine gap in the
conventional explanation before proceeding.

### 2. Test and prove the nuclear sorting reduction — about 3–4 hours

For a descending list of positive principal angles
`theta_1 >= ... >= theta_k > 0`, write

\[
 s(t)=\min\{4\sin(t/2),2\},\qquad
 e(t,u)=4\sin((t+u)/2).
\]

Let `B(t)` pair adjacent entries of a descending list, appending a zero when
its length is odd, and sum their e-costs; `B(empty)=0`. The exact target is

\[
 D_1(K,L)=\begin{cases}
 0,&k=0,\\
 \min\{B(\theta_1,\ldots,\theta_k),\;
       2+B(\theta_2,\ldots,\theta_k)\},&k>0.
 \end{cases}
\]

This statement is currently **unproved** in Lean. The old manuscript argument
is a conjectural proof sketch, not evidence that the normalization is complete.

Start with a bounded scratch calculation of exact finite matching minima and
the two proposed costs on small lists. Include empty/singleton cases, ties,
angles near zero, pi/3, right angles, and several distinct angles. Keep scratch
code outside the tracked source tree. These checks can reveal an obstruction;
their success is not a proof.

The proof route to examine is:

1. Resolve each singleton's minimum into a canonical or reflection choice.
2. Pair two canonical singletons at no greater cost, using the existing pair
   comparison. Pair two reflection singletons using `e(t,u)<=4`. Thus there is
   an optimal matching with at most one singleton of each type.
3. Move a reflection singleton to the largest angle using monotonicity,
   including a possible exchange with a canonical singleton.
4. Move a canonical singleton to the smallest remaining angle using the
   submodular exchange with a zero. Appending zero represents its canonical
   cost in the scalar formula; it is not a new geometric angle or reflection.
5. Normalize all remaining edges by the proved four-angle adjacent exchange
   and an actual induction that removes the two largest remaining vertices.
6. Account for parity and both singleton types. Construct the two patterns,
   prove both comparison directions, then connect the combinatorial result to
   `realTransportPowerMinimum_one_eq_nuclearMatching` and an ambient attainer.

Reuse `RealNuclearExchange.lean`; search pinned Mathlib/TauCeti and the current
involution/reindexing APIs before adding finite matching foundations. Keep
paper-facing results in DavisKahan. A reusable donor abstraction is justified
only if it simplifies this proof and has a genuinely general mathematical API.
Prefer a small induction with explicit cost identities to a large new framework.

**Acceptance:** Lean accepts the full finite normalization and ambient formula,
including k=0/1, ties, right angles and optional unmatched vertices. A theorem
for perfect matchings alone is insufficient. State any hypotheses on zeros
explicitly; the ambient interface must correctly filter positive labels.
The resulting sorting claim concerns a scalar arithmetic/comparison count,
not floating-point certification, bit complexity or a verified executable
sorting/matching implementation.

**Fallback:** if a counterexample appears, certify an explicit witness as far
as feasible and state the precise failed exchange or normalization claim.
If the statement remains plausible but proof progress stalls, preserve a
clear mathematical account of the unfinished induction and any compiled
substantive partial result. After roughly two hours without a clearer route
or a completed structural step, reassess; use the remaining proof allocation
only if it is moving toward the full theorem. Otherwise retain the exact
existing general-graph matching result and move to phase 3. Do not replace the
main target with an accumulation of unrelated helper lemmas.

### 3. Challenge novelty and prepare checkable examples — about 1–2 hours

Reuse the primary sources and authentication record in
[spectral-transport-unification.md](spectral-transport-unification.md),
[the historical review](historical-priority-review-2026-10-26.md), and the
existing novelty review. Extend the same provenance map where needed; do not
assemble another competing bibliography or census.

Attempt to derive the unrestricted real matching theorem from the closest
published statements. Prioritize Bolotnikov–Li–Rodman (2001), Problem 1.1,
Theorems 3.1/4.2/4.5 and Lemmas 3.2–3.3, then Davis (1958), Theorems 7.3/7.4,
Davis–Kahan Section 4, and the Qiu/Zhang trace-norm and Grassmann-metric work.
For every comparison specify field, objective, feasible set, norm/exponent,
value versus all optimizers, and any dimension or compatibility hypothesis.
If a predecessor implies our result, record the derivation and change the
novelty classification. If it does not, identify the exact missing conclusion.
Absence from the examined sources is not proof of first priority.

Use primary sources for new scholarly assertions. Give the Aubrun–Szarek
exercise lead a bounded authentication attempt only if an authoritative edition
is accessible; do not spend the night blocked by access or upgrade secondary
quotations to primary confirmation. No contacts or public priority claims.

Prepare two worked examples in dev documentation:

- The real four-dimensional repeated-angle witness at theta=pi/6: actual
  orthogonality and transport, canonical displacement spectrum
  `(2 sin(pi/12))` repeated four times, competing spectrum `(1,1,0,0)`, and
  nuclear costs `8 sin(pi/12)>2`. Reuse the verified counterexample.
- A list with at least three distinct positive angles: show the competing
  singleton/pair assignments and the actual optimal value. If a change of p
  changes the optimal matching, verify and explain it; do not assume such an
  example before calculating. Separate symbolic identities, certified Lean
  statements and numerical illustrations.

A perturbation-to-optimal-cost corollary is optional only after these outcomes
are secure. If it is mere substitution into an existing bound, label it an
expository corollary. Do not launch a new DK/QUENCH application campaign.

### 4. Validate, commit and report — reserve about 45–60 minutes

Retrieve `lake exe cache get` before Lake builds. Compile focused changed
targets during development, then run the full default `lake build` at the
final proof checkpoint. Keep successful output concise. Preserve public APIs
and update affected consumers and exact provenance rows by hand. Commit green
logical milestones on main with the model attribution required by AGENTS.md.
Publish resource accounting using the existing tool and commit its generated
ledger/totals separately before the final handoff.

Update the existing research plan and dated handoff with actual results,
precise declaration names/hypotheses, source comparison, build command/result,
and the strongest consequential next question. Leave unsuccessful proof
sketches clearly identified outside production imports; do not weaken theorem
statements or leave incomplete proofs in the accepted production checkpoint.

The morning report should answer:

- What is the hard unrestricted lower-bound argument, in ordinary mathematics?
- Is the two-sorted-sums formula proved, refuted, or still open, and exactly why?
- What changed about the algorithmic and novelty claims?
- Which examples and exact Lean declarations support the conclusions?
- What validation passed, and does another theorem materially help this paper?

## Scope boundaries and stopping rules

- No manuscript, visualization, submission, roadmap or other-repository edits.
  The user is actively revising the paper separately.
- Preserve preexisting user changes. Use one agent on main; no lane system,
  new verification scripts, dashboards or parallel provenance inventories.
- No ancestry campaign; retain existing attribution and consult it as needed.
- No generic-penalty, infinite-real-matching, exhaustive optimizer-topology,
  global-stability or concentration campaign during this run.
- Do not make publication readiness depend on proving sorting. A clean negative
  result or a precise unresolved boundary can strengthen the existing matching
  contribution.
- Stop when the proof explanation, sorting disposition, examples and targeted
  literature comparison are complete. Recommend focused writing and specialist
  review at that point; do not select another theorem merely to use the night.
