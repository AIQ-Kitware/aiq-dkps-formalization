# Operator Theory roadmap → course obligation audit

**Status:** mechanical enumeration plus curated proof-gap proposals; **not** a compiler extraction and **not** a claim of proof coverage.

The teaching baseline is basic linear algebra and calculus. The course must establish mathematical meaning and demonstrate proofs before treating a result as a dependency. A label in a paper, roadmap, or Lean file is not a substitute for an explanation.

## Audit denominator

- **899** unique, explicitly numbered obligations recovered from eight roadmaps.
- **6** Toeplitz stages are large prose chapters, **not six individual mathematical theorems**. Their result-level decomposition remains unfinished.
- **25** proposed proof-topic additions and **7** explicit proof-spine assessments.
- **0** currently written substantive TTS lectures verified by this audit (only the introductory TTS lecture has been drafted). Existing Manim lectures are source material, not accepted completion evidence.

## Per-branch provisional placement

| Roadmap | Obligations | Topic fit | Umbrella only | No current home | New proof node needed | Intended lane |
|---|---:|---:|---:|---:|---:|---|
| OrthogonalGeometry | 14 | 6 | 7 | 0 | 1 | core |
| PolarDecomposition | 121 | 58 | 54 | 0 | 9 | core |
| Majorization | 79 | 24 | 32 | 0 | 23 | core |
| PrincipalAngles | 97 | 27 | 68 | 0 | 2 | core |
| SelfAdjointSpectralTheory | 274 | 96 | 173 | 0 | 5 | core |
| OperatorIdeals | 169 | 56 | 93 | 0 | 20 | core |
| SpectralSubspacePerturbation | 95 | 33 | 35 | 0 | 27 | core |
| MatrixSpectralStatistics | 50 | 5 | 17 | 0 | 28 | extension |

**Meaning:** “topic fit” is name/scope similarity only. “Umbrella only” means the roadmap result has only an approximate unit-level home. The new-node column counts obligations flagged for specific missing proof development. None of these categories means a proof has been taught.

## Highest-leverage proof gaps

1. **`SSP-A01–A26`, `SSP-B13`:** develop Fourier/Laplace tools, odd-pole/Poisson calculation, HZ kernel, its π/2 mass and operator-valued integration; the pairwise Sylvester estimate cannot be understood from the title “norm dependence” alone.
2. **`SA-C55` and unbounded Sylvester obligations:** develop Kato–Rellich, graph/domain transfer, Cayley and resolvent identities, cutoff convergence. State exactly when a perturbation preserves self-adjointness.
3. **`MAJ-A*`, `MAJ-B21`, `PA-B40`:** supply the convexity, Schur–Horn/Birkhoff, Karamata and rectangular Fan-dominance proofs and the eigenvalue-change proof.
4. **`OI-C*`, `OI-A*`, `OI-B*`:** reconstruct Hilbert–Schmidt Hilbert-space structure, approximation-number limits, symmetric gauges, and ideal membership; distinguish finite unitarily invariant norms from infinite ideals.
5. **`SA-B*` and `SA-E*`:** prove scalar-measure representation, PVM additivity, Borel calculus and unbounded spectral-measure construction rather than citing a finished spectral theorem.
6. **`PD-C20` and neighboring obligations:** teach Moore–Penrose inverse with four Penrose equations and the noninvertible rectangular cases.
7. **`MSS-A*`, `MSS-B12`, `MSS-C*`:** develop rank/Gram factorization, random-projector measurability and matrix concentration for the extended statistical branch.
8. **Toeplitz `T1–T6`:** do not fold Hardy/Fredholm/K-theory into the compulsory Davis–Kahan chain. Give it an explicit separate scope and a future supplier dependency audit.

## Mathematical proof-spine tests

Each proof-spine entry in `proposed-proof-nodes.json` gives prerequisites and a reconstruction task. A real assessment must make students derive the stated intermediate lemmas, show the needed hypotheses and explain the controlling example/counterexample.

## Existing graph ordering conflicts

New proof nodes and `feeds` edges were kept separate from the old DAG. Topological consistency of the combined proposals: **PASS**.
No newly proposed cycles were found; the new nodes can be inserted into a valid order, subject to pedagogical review.

## Coverage rules for subsequent drafts

- **Not introduced:** neither construction nor motivating example has been written.
- **Introduced:** learner can say what it means and compute a basic example.
- **Explained:** learner can reconstruct why the statement should hold and find a failure case when assumptions are dropped.
- **Proved:** transcript gives a complete, correctly scoped argument with intermediate lemmas and checks.
- **Lean-correlated:** current pinned Lean declaration and all meaningful hypotheses have been checked and interpreted in the lesson; this is separate from mathematical proof coverage.
Only the last two categories together make a proof-producing lesson ready for use as a proven prerequisite; the source ledger currently assigns neither.

## Evidence and limits

- Roadmap IDs and titles extracted from the user-provided roadmap READMEs with source line numbers; `Suggested.lean` contains only representative signatures, not a complete declaration index.
- The baseline DAG is a teaching DAG, not the transitive compiled Lean constant graph. The present overlap matching is explicitly provisional; all `unit_only` matches demand manual review.
- Existing upstream status is not verified by this attachment. Snapshot progress/status logs are historical and may not describe the current pinned TauCeti API.
- Toeplitz stages are prose; a result-level denominator requires splitting each T1–T6 stage into theorem-sized obligations.
- External prerequisite supplier roadmaps for Banach-space theory, one-parameter semigroups, C*-algebras and operator K-theory are **not** included in this attachment; list these as unresolved boundary dependencies rather than silently claiming first-principles completeness.

## Lean evidence to request

Use `lean-evidence-request.md` for a small, targeted export from a locally built repository. The most valuable evidence is **the declaration-level graph of constants referenced in the proof terms of the final DK theorems**, recursively through TauCeti / ForTauCeti until the chosen Mathlib boundary. Simple import graphs or regex scans are not substitutes.
