# Recent campaign briefs are GPT-authored, relayed by the human

**Date:** 2026-08-07 (Claude Opus 5, at Edward's request)
**Severity:** low — provenance note, not a bug. Read it before treating a brief
as ground truth.

## The fact

The long, highly structured campaign briefs driving these sessions (the
Section 8 close-out, and the several sessions before it) are **written by GPT**
and relayed by the human. They are not the human's own words, and they are not
verified repository state.

This is the same class of input as the 2026-06-14 entry in
[`lessons_learned.md`](lessons_learned.md), "Over-relying on a ChatGPT
*rephrasing* of reviewer feedback" — but one level up: not a rephrasing of
someone's feedback, an authored plan.

## How they have actually behaved

Better than that precedent suggests, and it is worth saying so rather than
manufacturing a cautionary tale:

- The Section 8 brief's "DO NOT REDO THIS MATHEMATICS" inventory was accurate —
  every declaration it named existed and was green.
- Its object definitions were mathematically right, including the non-obvious
  part: `lowerBlockShift` carries the shift `α + δ`, not `α`, because the mirror
  of the upper clause is `A ↦ -A`, `α ↦ -(α + δ)`.
- Its proof recipes were right. Both lower-block modules compiled on the first
  attempt from the brief's step list.
- It correctly refused a trap the repository's own census had walked into:
  "do not simply add `IsQuarterAcute P Q` as a hypothesis to a theorem whose job
  is to prove the quarter-angle result", and it pointed at the right existing
  lemma to look for.

## Where the risk actually was

**Not in the brief — in the repository prose the brief inherited.**

- `dev/section8-source-theorems-2026-08-07.md` still said parts (ii) and (iii)
  had not landed, after the upper block had.
- The census `next_action` for DK-8.1-thm prescribed
  `LinearMap.IsSymmetric.eigenvalue_mono` for part (ii). That is
  finite-dimensional and would have forced a subspace transfer of the whole
  development and a strictly weaker theorem. The brief contradicted it ("do not
  overcomplicate it with finite-dimensional eigenvalue APIs") and was right;
  `approximationNumber_mono_of_form_le` does the same Weyl step in arbitrary
  dimension, which is what delivers the printed "natural infinite-dimensional
  extensions".

The one place a **literal** execution of the brief would have produced a false
statement: Part C2 asked for "singular values of `C_i` = `cos(theta_i)` with the
source's ordering convention". The repository's `principalAngles U V` is
`arcsin` of the *sine*-block singular values, and `principalCosines U V` is the
*cosine*-block singular values; both are sorted decreasingly, so
`cos (principalAngles U V i) ≠ principalCosines U V i` — the orders are
reversed. The true bridge is against `principalCosines`, which is also the
paper's own equation (1.16) (`Θ_j = arccos (C_j C_j⋆)^{1/2}`). Stating it
against `principalAngles` at a shared index would have compiled as a goal and
been wrong.

## Takeaway

- Treat a brief's **claims about repository state** as a hypothesis and probe
  them; treat its **proof recipes** as a strong first guess, which they have
  been.
- Where a brief and a census/handoff disagree, neither wins by default. Check
  the source and the declarations.
- An ordering or indexing convention named in prose ("with the source's ordering
  convention") is exactly where an authored plan cannot have checked itself.
  That is where to look first.
