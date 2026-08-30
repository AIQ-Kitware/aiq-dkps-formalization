# Outstanding work

Written 2026-08-29, from the verified state at `a686dbc6`.  **Lanes A5, B, C and I
are done as of 2026-08-29, and lane A's architecture changed; see the status notes
in each.** The previous campaign
brief — the Frontier / MathAhead / Experimental cleanup, completed 2026-08-27 — is
in Git history; `docs/planning/historical/README.md` is explicit that Git is the
default archive for completed campaigns.

Read `AGENTS.md` first. For anything Palomar, `dev/palomar-readiness.md` is the
execution contract and its §1 decisions are not an agent's to revisit.

This is a mature formalization. Nothing below is a rescue; it is the list of things
that would still be improvements, ordered so that a session picking one up knows
what it is buying.

**Already done, and not to be reopened without a real bug:** the
Frontier/MathAhead/Experimental cleanup; `RectangularSymmetricIdealFamily`;
`ClosedOperator` → Mathlib `LinearPMap`; the removal of all three Git submodules;
Tau Ceti as a pinned Lake dependency. The last two are load-bearing for Palomar —
Lake clones a dependency without initialising submodules, so a submodule makes this
repository unusable as one.

---

## A. Palomar

Two entries are prepared and pass the real Comparator (`registry/yws-2015`,
`registry/dk-1970`). Preparation only; **an agent must not submit.**

**A0. Superseded 2026-08-29: the entry repos carry the proof.** Maintainer decision.
Each entry is now an **extraction** rather than a thin wrapper — it contains the
package directories it needs, copied verbatim, and builds them itself.
`aiq-davis-kahan-1970-…` carries `ForTauCeti` + `DavisKahan`;
`aiq-yu-wang-samworth-2015-…` carries those plus `YuWangSamworth2015`, the
Davis–Kahan library being there for the ideal theory the YWS package uses. Both are
`repository.role: substantive-development`, both pin the same Mathlib and Tau Ceti as
this repository, and both were built green from a clean build directory (8739 and
8732 jobs). The census, source specification, audit apparatus and gates are
deliberately not extracted, so neither repository makes a completion or coverage
claim about its paper. `dev/palomar-readiness.md` §5.0 is the record; §5.1 onward is
the superseded design, kept because its submodule reasoning still holds. **A1 below
no longer applies** — there is no wrapper SHA to fill.

~~**A1. Wrapper commit SHAs.** Each `registry/<entry>/wrapper/` has
`REPLACE_WITH_COMMIT_SHA` in `lakefile.toml` and `formalization.yaml`. Filling them
is a maintainer step at submission time, against the commit actually verified.~~

**A2. Maintainer review before any submission.** The checklist is
`dev/palomar-readiness.md` §12. Registration is permanent.

**A3. A second Yu–Wang–Samworth entry: Theorem 2's aligned-frame conclusion.**
`YuWangSamworth2015.theorem2_alignedFrame` is the printed second conclusion, with
the `2^{3/2}` constant and the orthogonal matrix — good material, deliberately left
out of the first entry to keep it auditable. It needs `IsEigenvectorBlock`,
`SourcePopulationGap` and `PopulationBoundaryGap`, so the design question is whether
to inline them or to compare them through `definition_names`. The latter is untested
here; prove the machinery on something small before relying on it.

**A4. DKPS entries.** Deferred by maintainer decision (D4), not by feasibility.
`dev/palomar-readiness.md` §6.5 measures what each would cost: Acharyya 2024 needs 4
real definitions restated, Quench 5, Acharyya 2025 9 including the classical-MDS
construction, Helm 15 — which is why Helm is not currently practical. That table is
the starting point if JHU picks any of these up.

**A5. DONE 2026-08-29, and the earlier note here was wrong.** It claimed the
installer's three gaps were fixed. Running it on a clean machine on 2026-08-29
showed otherwise, and there were five:

- `go env GOPATH` ran unguarded under `set -e`, so on a machine with no Go the
  script died at line 39 and never reached the graceful "landrun is only the
  sandbox" path twenty lines below it;
- the toolchain pin reached the comparator checkout but **not** its nested
  `lean4export` package, which is the binary that actually reads our oleans — so
  a tree whose top-level toolchains matched still failed with `incompatible
  header`, the exact failure the pin exists to prevent;
- the update path fetched `origin main`, but comparator's default branch is
  `master`, so a second run of the installer aborted.

All five are fixed and the installer is idempotent. It now also verifies the pin
took, by asking `lean4export` which Lean it reports. The original note follows.

~~`scripts/install_comparator_tools.sh` is incomplete, and both gaps cost real
time.~~ It does not install NanoDa at all, which is the second independent kernel and
a genuine check rather than a sandbox. And it does not address the toolchain pin:
Comparator pins its own Lean, which was `v4.34.0-rc2` against this repository's
`rc1`, and `lean4export` built at the wrong version fails on our oleans with
`incompatible header` — the exact failure class
`dev/journals/comparator-statement-export-matching-2026-06-14.md` already warns
about. Working commands are in `dev/palomar-readiness.md` §6.4; folding them into the
installer is small and obviously worthwhile.

---

## B. Davis–Kahan 1970 — DONE 2026-08-29

All nine rows are settled. The census now reads 45 `compiled_exact`, 3
`not_a_completion_obligation`, 1 `refuted_as_transcribed` (the false Proposition
4.4, with its counterexample and repair preserved) and 1
`resolved_by_modern_development`. No row is `partial_or_wrapper_missing`, and both
`hostile-source-facing-gap` and `hostile-source-spec-fidelity` are retired.

Four rows needed new mathematics: `principalPlaneChord_eq_two_mul_sin_half` (the
half-angle identity that had only been asserted in a docstring, and on which
DK-4.1's binding of the printed `2 sin(θ/2)` rested), Example 6.1 as a compiled
counterexample, the arbitrarily small domain repair for the infinite-residual
example, and the free-beam eigenvalue-ordering assembly. The other five needed the
boundary record to say what the source actually claims — attributed, sharpness,
motivation or open-question material, dispositioned rather than converted into
theorems the paper does not assert.

One correction worth keeping: reverse links in the atom inventory are *derived*
from each counted result's own `source_atom_ids`, so a reverse link asserts
membership of that result's source block. Linking a Section 10 restatement to the
Section 2 theorem it restates is wrong; the empty link plus a specific boundary
reason is right. The result-inventory checker catches the mistake.

The original lane text follows, as the record of what was asked.

### Original lane B

The 29-result completion inventory is terminal and must stay that way. Do not turn
exposition, examples or open questions into new denominator results. The rows below
are in the 50-row source-fidelity census, which is a different and larger thing.

**Do the mapping-stale ones first.** Each may already be closed by a theorem that
landed after the audit that reopened it; re-read the source passage and the current
Lean before proving anything.

- **`DK-3.2-prop`** — nonacute existence criterion. The census says the source-facing
  crossing-square-minus-one theorem now exists; the row is partial because the hostile
  audit predates it. If it closes the atom, fix the mapping. Do not prove a duplicate.
- **`DK-4.1-prop`** — pointwise and singular-value extremality. Equations (4.1) and
  (4.2) were restored in the distributable TeX; this looks like binding the minimax
  and pointwise-angle atoms to existing evidence, not new mathematics.
- **`DK-9-model`** — fourth-derivative Rayleigh–Ritz. Substantial real/complex and
  beam-spectrum work has landed since the row was last written. Re-audit the current
  code and atomization from scratch rather than trusting the prose snapshot.
- **`DK-10.4`** — functional calculus. A mixed block: the step-function and `tan 2Θ`
  specializations are established mathematics and belong in the census as such; the
  final general-functional-calculus question is open and is not a proof obligation.
  Split them.

**Then the ones with genuine mathematics left.**

- **`S1-block-residual`** — the standard residual-to-eigenvalue consequences,
  `∑ⱼ (αⱼ − λⱼ)² ≤ ‖R‖²` and `|αⱼ − λⱼ| ≤ ‖R‖₁`. Search Mathlib, Tau Ceti and the
  current tree before proving; the Rayleigh-quotient minimisation may already be there
  and only need registering.
- **`DK-5-hermitian-inequalities`** — the source says (5.2) is not best possible unless
  `rank C ≤ 1`. (5.1), the rank-corrected estimate and a counterexample to the constant
  already exist. Determine the exact logical content of the source's stronger
  qualitative claim; do not formalize an English sentence as a theorem stronger than
  the source supports, and split the adjacent open question from the established
  assertion.
- **`DK-6.3-thm`** — Example 6.1, if absent: `δ = 1`, tangent quantity `1`, residual
  `1/√2`, spectral mass on the wrong side. A source-fidelity example, not a headline.
- **`DK-9.8`** — the largest remaining piece. Weinberger sine-square, the Lehmann
  best-lower-bound assertion, the `O(ε⁴)` asymptotic, and the (9.8) conclusions. For
  each: decide whether it is a theorem Davis–Kahan establish, an attributed external
  fact, an asymptotic calculation or commentary, and disposition it honestly. Do not
  turn an attributed external theorem into a local axiom.
- **`DK-9-infinite-residual-counterexample`** — the finite truncations already lie in
  the domain and agree on every fixed prefix; what is missing is norm convergence, or
  an arbitrarily small modification repairing the domain defect.

**Rows reopened by hostile re-audit but currently `compiled_exact`** — `S2-sharpness`,
`S2-unbounded-scope`, `DK-3.1-def`, `DK-4.2-prop`, `DK-4.3-prop`, `DK-5.1-thm`,
`DK-5.2-thm`. Each carries a note saying what the audit questioned. These are
audit-disposition work, not proof work, unless the re-read says otherwise.

**Preserve:** the refuted Proposition 4.4 with its counterexample and Q-norm repair;
the accepted nonlocal reading of the Section 2 tangent theorem; and the four genuinely
independent proof roots (elementary finite eigenbasis, finite Sylvester/operator,
arbitrary-dimensional bounded, full unbounded). Overlapping statements are not a
reason to collapse independent proofs.

---

## C. Acharyya 2024 — DONE 2026-08-29

The re-audit found the defect class it was told to look for, in a milder form than
the pass that prompted this lane, and in both of the two shapes named below. Both are
hypothesis-side, so the fixes strengthen the theorems rather than correct them; no
conclusion moved and no proof needed new mathematics. Commit `09cdd30a`.

*Quantified over more than the proof uses.* The pointwise theorems are about one pair
`(i, i')` and their proofs touch no other model, but their integrability, moment and
rate hypotheses were stated at every model index. They now ask only at `i` and `i'`.
This runs through the growing, random, gamma, kernel and product variants, so the
pairwise T5 statement — the one drawing both models of the pair independently — now
needs its sampling hypotheses only along the pair it is about.

*Eventually-quantifier outside a binder that could hold it.* The finite-collection
theorems asked for one stage threshold valid for every query at once. There are
finitely many queries, so per-query thresholds combine; the hypothesis is now the
per-query one and `Filter.eventually_all` does the combining inside the proof.

The other shapes on the list — a zero-stage artifact, a product measure where a kernel
is needed, fresh-query versus sampled-pair confusion, an ε-dependent subsequence, an
integrated assumption stronger than dominated convergence needs — were looked for and
not found. The kernel route in particular is domination by `1` in kernel generality
and asks for no uniformity over the model population, which is what it was built to
avoid.

The original lane text follows, as the record of what was asked.

### Original lane C

Every census row's `next_action` is `None`, and T2/T4/T5 were substantially
strengthened on 2026-08-28. What remains is a **hostile re-audit of the final
T2/T4/T5 surfaces**, looking for another defect of the kind that pass found — a proof
needing only a fixed pair while the statement quantifies uniformly, an `∀ᶠ` in the
wrong binder order, a zero-stage artifact, a product measure where a kernel is needed,
fresh-query versus sampled-pair law confusion, an ε-dependent subsequence, or an
integrated assumption stronger than dominated convergence needs.

If nothing is found, leave the mathematics alone and say so. Do not refactor a working
theorem to create activity.

---

## D. Acharyya 2025

- **`A25-T1`** — state the corrected finite concentration bound as one theorem with
  the entrywise dissimilarity bound `R` explicit. The pieces are compiled and the
  counterexample showing `R` is necessary already exists; this is the honest
  source-facing endpoint, and the repair belongs in the name and docstring.
- **`A25-C1`** — one source-facing declaration for the spectral-norm `r = ω(n³)`
  corollary, if it really is a single assembly step. Recognizability, not new
  mathematics.
- **`A25-P1`** — the printed compact-Riemannian condition does not force the
  nondegeneracy the argument needs. If a repair is wanted, formulate a meaningful
  spread condition and prove Assumptions 1 and 2 from it. **Label it a repair; it is
  not the printed proposition.** Lower priority than T1 and C1.
- **`A25-PA1`–`PA6`, `L1`–`L5`** — optional source-fidelity wrappers, role-replaced by
  cleaner perturbation machinery. Lowest priority; skip unless a Palomar entry or a
  reader needs them.

---

## E. Helm 2025

- **`H25-EQ2`** — expose one Helm-facing statement of the displayed
  sample-dissimilarity-to-population limit. It exists by composition, and it is also
  the input the eigengap-free bridge wants. Bounded and worth doing.
- **`H25-BRIDGE`** — fiber `Acharyya2024.rawStress_mds_stability_set` over the latent
  sample to discharge the bridge's distance-convergence hypothesis. If it works, the
  Helm bridge weakens accordingly.

**Preserve** the uniform-integrability / dominated-loss repair and the evidence that
convergence in probability alone does not give expected-risk convergence. That is a
real finding about the paper, not an inconvenience.

---

## F. Quench 2026

- **`Q26-T2A` / `T2B` / `RAW-FIN` / `RAW-INF` — remove the finite perspective net on
  the compact-infinite route.** Likely the highest-value new theorem work in this list.
  The finite route already runs at the source rate; the infinite route carries an extra
  finite perspective net, and Acharyya 2024 now has a genuine continuum/population-law
  route that may replace it. Do not force it past a real compactness or measurability
  obstruction — if it fails, name the precise theorem that would be needed.
- **`Q26-T1`** — inherited embedding concentration. Either generalize the rate theorem
  to a growing sample with an augmented target, or keep the divergence explicit. Check
  first whether the strengthened Acharyya 2024 machinery closes it.

**Preserve** the tie-averaged nearest-neighbour estimator, the correction of the false
all-compact-subsets assumption, and the adjudicated `1/m` normalisation with its two
invariance theorems.

---

## G. Yu–Wang–Samworth 2015

The census is complete at 24/24. **Do not open a YWS proof campaign.**

- One **current-state review pass**: stale references after recent refactors, hidden
  added hypotheses, quantifier order, rank-boundary corners, and local implementation
  definitions leaking into public statements.
- **`YWS-T1-eq1`** — optional literal indexed Equation (1) wrapper. The source display
  omits the simplicity hypothesis needed to identify a single sample eigenvector line.
  If added, make that hypothesis explicit and classify it; do not manufacture an
  "exact" wrapper that hides it.

**Preserve** the corrected Equation (4), which is false as printed, and the corrected
rank-boundary convention.

---

## H. Cross-paper coherence

Worth one pass after the per-paper work, because these are the places a stronger
theorem landed without its consumers being moved:

- Does Acharyya 2025 consume the strongest YWS population-gap theorem, or an older
  specialization?
- Are obsolete eigengap or perturbation assumptions still sitting on source-facing
  capstones after the YWS integration?
- Does Quench consume the strongest current Acharyya 2024 result rather than a
  fixed-sample specialization?
- Can Helm consume the improved Acharyya raw-stress bridge?
- Any duplicate "temporary" theorem surface that survived a stronger theorem landing?
- Are source-facing names and docstrings still accurate after the `ClosedOperator` →
  `LinearPMap` and continuum-probability migrations?

Do not over-abstract across papers because implementations look similar. Paper-facing
wrappers earn their place through source correspondence.

---

## I. Known debt — partly done 2026-08-29

The four `sorry` comments are fixed, and a fifth was found in
`RoadmapBridge/MatrixSpectralStatistics.lean`; no Lean source contains the word
now. Separately, four comments claiming axiom cleanliness were deleted, and the
AGENTS.md rule that failed to prevent them was narrowed: it banned the word
`axiom` in any comment, which cannot be complied with, since around forty comments
use it in its ordinary mathematical sense. It now bans axiom-status boilerplate and
permits the mathematical usage.

The three gate failures below remain, deliberately.

### Original lane I

Listed so nobody mistakes them for regressions, and so nobody "fixes" them by lowering
a baseline or deleting a check.

- **`check_expose_ratchet`** — 166 per-declaration `@[expose]` against a baseline of
  10. Upstream API-design debt; it does not weaken any mathematics, and the count
  already fell organically when obsolete consumers disappeared.
- **`check_tauceti_readiness`** — 70 blockers, mostly `UNPLACED` modules. The upstream
  package is waiting on review; assigning roadmap topics to make a gate green is not
  work.
- **`check_tauceti_roadmap_topics`** — 69 violations. One is a genuine design finding
  worth someone's attention: a forward reference `T09 → T23` between
  `ApproximationNumber.GramSquare` and `ApproximationNumber.GramSpectralRank`, which
  would stop that topic being submittable in order. The rest are unassigned modules and
  the roadmap-coverage layer, which now reports `UNAVAILABLE` when no external roadmap
  checkout is supplied.
- **Four comments contain the literal word `sorry`**, which `AGENTS.md` forbids because
  it defeats grep-based detection — `DavisKahan/InfiniteDimensional/DoubleAngle.lean:631`,
  `DavisKahan/InfiniteDimensional/TanTwoTheta/CanonicalTangentBridge.lean:308`,
  `DavisKahan/Geometry/Halmos/GenericRotationPredicates.lean:16`,
  `DavisKahan/Experimental/All.lean:33`. Cheap; fix them in whatever commit next touches
  those files.

---

## J. Presentation — only after the above

- `leanq` HTML dependency visualization. Keep its design constraints: generic over
  census families, package-first compound layout, Mathlib boundary summarised and its
  internal edges hidden by default, no initialization race. Do not replace the existing
  viewer.
- `doc-gen4`. Nice, not required by Palomar. Do not spend a campaign on documentation
  infrastructure while source gaps remain.

---

## Standing rules

Do not weaken a theorem, hide a hypothesis inside a definition, or substitute an
implementation-specific surrogate for a recognizable notion to make a checker, a census
or a Challenge go green. Do not convert a documented source repair back into a claimed
exact theorem. Do not delete a counterexample that shows a printed statement false. No
`sorry` in production mathematics, no custom axioms, and no `native_decide` anywhere —
it introduces `Lean.ofReduceBool`, which no Palomar Solution may depend on.

Do not add Git submodules. Do not add a new `scripts/check_*.py` without asking; the
two Palomar ones were an explicit maintainer exception.

Report status in terms of the mathematics. A green build certifies compilation and
declaration resolution, never source fidelity — that is what the censuses and semantic
reviews are for, and they exist to record disagreements with the printed papers rather
than to hide them.
