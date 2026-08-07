# Full-paper completion plan: the road to 100% (except DK-4.4)

Written 2026-08-06, immediately after Section 3 closed (Hahn--Hellinger uniqueness included).
Scope set by Edward: **paper-faithful theorems for everything in Davis--Kahan 1970 Part III,
excluding DK-4.4-prop**, which is `refuted_as_transcribed` and litigated; do not reopen it.

Authority for statuses: `dev/davis-kahan-1970-full-source-census.json` (CLEAN 48/48, probe
162/162 against `DavisKahan.All` as of commit `4f2c71b2`).  **Verify every row against the
build before writing code** -- five rows this week (3.1-def, 3.2-def, 3.3, 3.4, 3.5) asked for
things that already existed.

## What is already done

Sections 1--8 numbered results: `compiled_exact` + `proved_in_build` everywhere except the
items below.  All of Section 3 including uniqueness.  Section 10 rows are the paper's own open
questions -- documented, not proof debt.

## A. Section 9 -- the numerical example (the bulk; only `proved_conditional` rows anywhere)

The arithmetic layers compile; the analytic inputs are ASSUMED via certificate fields
(`TheoremOutputCertificate`, `FreeBeamFiniteDataCertificate`), not derived.  To 100%:

1. **DK-9-model.**  Construct the closed free-beam fourth-derivative operator on `L²(0,1)`
   with the source's boundary conditions; self-adjointness; enough spectral theory to
   discharge **`α₃ > 500`**.  The hard analytic formalization: unbounded operator with domain
   conditions and an eigenvalue lower bound.  Until a value exists, Section 9's conclusions
   are assumed, not derived.
2. **DK-9.1--9.4, DK-9.5--9.7.**  Replace certificate fields by applications of the
   source-facing sine/tangent/double-angle theorems (all proved), so printed conclusions are
   derived.
3. **DK-9.8.**  Weinberger-comparison root inequality; needs the `α₃` bound from item 1.
4. **DK-9.9--9.11.**  The rank-one resolvent order argument (individual eigenvectors inside a
   cluster); replaces the last certificate fields.
5. **DK-9-infinite-residual-counterexample** (`compiled_specialization`).  Sequence lemmas are
   unconditional; optionally lift from coordinate sequences to the abstract operator setting.

## B. DK-6.3-lem (`partial_or_wrapper_missing`)

Finite-rank near-maximizer leakage estimate -- the only numbered result in Sections 1--8 whose
exact source statement is neither proved nor wrapped.  Self-contained approximation-number
statement; reusable for cutoff passages.

## C. Section 7 proof rows (`compiled_general_infrastructure`)

- **DK-7-sin2-proof.**  The sin 2Θ theorem is exact; the row wants a source wrapper
  preserving BOTH conclusions of the paper's reflection proof (residual and perturbation)
  together.
- **DK-7-tan2-proof.**  "Complete the exact source norm scope and infinite-dimensional
  approximation passage" for the singular-vector proof.  Re-audit first; may be partly stale.

## D. DK-3.2-cor -- Section 3 straggler

Reversal symmetry compiles under `DavisKahan/Experimental/FiniteDimensional/DirectRotation.lean`
-- NOT guarded by any default target.  Promote into `DavisKahan/FiniteDimensional` (CI guard),
then add the source-facing angle and quarter-turn statement.

## E. Audit-and-normalize (probably little or no mathematics; verify first)

- **S2-tan-two-theta** (`compiled_specialization`): its recorded blockers point at rows now
  `compiled_exact` (S2-unbounded-scope, DK-6-appendix), and its note that DK-8.1/8.2 are
  outside the default build is stale -- both are `proved_in_build`.  Re-audit; likely
  upgradeable, possibly with a residual unbounded-tan2Θ passage to check.
- **Repo-wide `sorry` sweep** of the guarded trees: an old note claims one Experimental module
  in a 42-module closure still carries a `sorry`.  Enumerate and either prove or confirm
  out-of-scope.
- **DK-10.1**: record precisely which norm classes are resolved and which remain open
  (documentation, not proof).
- Statuses on rows whose next_action says "nothing outstanding" (`S1-*`, DK-3.1-thm,
  DK-3.1-cor, DK-3.2-prop): conservative labels only; normalize or leave.
- Optional hardening recorded on DK-3.4-prop: compile the two prose counterexamples pinning
  the corrected hypothesis shape (explicitly not proof debt).

## Working rules carried forward

Serial, no subagents.  Never pipe `lake build`.  One build at a time.  Commit and push at
every milestone; Edward reviews from the pushed state.  Author new files as the model actually
running.  Frontier shortfall (12 ungrounded nodes, 5 ungrounded paper results) is exactly
Section 9 and will close with part A.
