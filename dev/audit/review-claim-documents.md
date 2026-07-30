# Review — the claim documents of `FinishYuWangSamworth` and `FinishTanTwoTheta`

**Lane `CLAIM-DOC`, second half. 2026-07-30, `edward (aiq-gpu)`.** The first half
(running and gating both `verify_grounding.py` scripts) was done by
`jon (yardrat)`. This is the remaining half: reading `PROOF_OBLIGATIONS.md` and
`ELEGANCE_AUDIT.md` against the tree.

These matter more than ordinary documentation because they are what a reader
trusts *instead of* checking. A false claim here is worse than a weak proof.

## `FinishYuWangSamworth` — both documents are accurate

I posted this lane suspecting staleness. **`ELEGANCE_AUDIT.md`'s five claims all
verify**, checked declaration by declaration:

| claim | verified |
|---|---|
| One Frobenius ideal foundation, consumed by Lemma 5 rather than repeated | `Rectangular/FrobeniusGram.lean:95` defines `rectangularFrobenius_twoSided_comp_le`; `Appendix/Lemma5.lean` consumes it at lines 41 and 151 |
| Source-shaped Lemma 5 entry points via bundled isometries | present in `Appendix/Lemma5.lean` |
| No manual dimension witnesses — `[Nontrivial E]` instead | `Theorem4.lean:278,284,300` |
| Shared right/left core kept `private` | `private theorem` at `FrobeniusGram.lean:38`, `Lemma5.lean:92,168`, `Theorem4.lean:60,70` |
| Equation (4) counterexample machine-checked | `Symmetric/AngleIdentity.lean:40` `yuWangSamworth_equation4_printed_counterexample`, closed by `norm_num` |

**`PROOF_OBLIGATIONS.md` agrees with the census**, which is the stronger test
because the census is generated from the paper rather than from the Lean:

- It claims every numbered result has a theorem surface — Theorem 1, Theorem 2,
  Corollary 3, Theorem 4 (right and left), Lemma 5. The census marks all of
  these `compiled_*`. **True.**
- Its "remaining non-numbered work" names the two sharpness examples. The census
  marks exactly two items `not_represented`: `YWS-S2-sharpness-orthogonal` and
  `YWS-S2-sharpness-planar`. **True, and precisely scoped.**

That is a document that has been maintained. Recorded as such.

## `FinishTanTwoTheta` — `PROOF_OBLIGATIONS.md` is stale `{lane:CLAIM-DOC}`

The document states:

> The immediate remaining obligation is **compiler validation and repair** of
> these written arguments without narrowing the theorem. After compilation, run
> the repository grounding checks and `#print axioms` on the unrestricted
> theorem.

**That obligation is discharged.** Commit `9d9ebb4a`, *"FinishTanTwoTheta
COMPILES: the unrestricted bounded tan(2Θ) theorem is proved"*, landed on
2026-07-30; `paperFaithful_tanTwoTheta_uiNorm` is at
`DavisKahan/PaperFaithful.lean:408`; and the library carries **0 proof escapes**
across all 21 modules.

So the document describes a pre-compilation state that no longer exists. A
reader arriving today is told the central theorem is written but unvalidated,
when it is proved. **Fix:** replace the "immediate remaining obligation"
paragraph with the compiled status and whatever genuinely remains — the document
itself names two candidates, the axiom audit on the unrestricted theorem and the
separate unbounded sharp ideal theorem.

## Both libraries — the gap neither document mentions

**Neither `FinishTanTwoTheta` nor `FinishYuWangSamworth` is in
`defaultTargets`.** `lakefile.toml:6` lists `ForTauCeti`, `DavisKahan.All`,
`Acharyya2024`, `Acharyya2025`, `DkpsQuench2026`, `Helm2025` — and neither
`Finish*` library.

The Yu–Wang–Samworth census already quantifies the consequence: **19 items
formalized, of which only 10 are guarded by the default build.** Nine proved
results can be broken by a refactor while every gate stays green.

Both claim documents assert coverage without saying this. That is not a false
claim — the results *are* proved — but it is the omission a reviewer would
object to, because "formalized" and "protected against regression" are different
properties and only one of them is stated.

**Fix:** one sentence in each `PROOF_OBLIGATIONS.md` recording that the library
is not a default build target, and what that means. The deeper fix — adding the
targets — is lane `FTT-PROMOTE`'s territory for `FinishTanTwoTheta`, and is
noted in the census for `FinishYuWangSamworth`.

## Verdict

| document | verdict |
|---|---|
| `FinishYuWangSamworth/ELEGANCE_AUDIT.md` | **accurate** — 5 of 5 claims verified |
| `FinishYuWangSamworth/PROOF_OBLIGATIONS.md` | **accurate** — agrees with the generated census |
| `FinishTanTwoTheta/PROOF_OBLIGATIONS.md` | **stale** — its stated remaining obligation is done |
| both `GROUNDING.md` | done by `jon (yardrat)`, scripts now gated |
| both | **incomplete** — neither says the library is unguarded by the default build |
