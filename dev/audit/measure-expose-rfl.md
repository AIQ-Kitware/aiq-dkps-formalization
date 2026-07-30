# `:= (rfl)` removes the need for `@[expose]` — measured, not argued

**Lane `FTC-EXPOSE-RFL`, run 2026-07-30 by `edward (aiq-gpu)`.** This settles the
question [`measure-expose-conversion.md`](measure-expose-conversion.md) left
open, and it **overturns that report's Result 2**.

That report found every in-module failure was a `_def`/`_apply` restatement
proved by bare `rfl`, and concluded the fix is `@[expose]` on the definition —
*"the rubric's own carve-out."* But `rubrics/api-design.md` offers a different
remedy in the same sentence, and the measurement never tried it:

> Recall that we can avoid making lemmas rely on defeq downstream by using
> `:= (rfl)` instead of `:= rfl`.

**It works. `@[expose]` is not needed.**

## The experiment

`ForTauCeti/Analysis/Fourier/HaagerupZsido/Defs.lean` — chosen because it
carries **four of the eight failures** the earlier report observed, in one file.

| variant | `@[expose] public section` | `_def` proofs | result |
|---|---|---|---|
| baseline | yes | `:= rfl` | green |
| **A** | **no** | `:= rfl` | **4 errors**, `Not a definitional equality`, at lines 36/94/103/112 |
| **B** | **no** | **`:= (rfl)`** | **green** |

Variant A reproduces the earlier report exactly, which is what makes B
meaningful: same file, same four lemmas, one character of difference each.

## The downstream cascade is real, and it is one site

The earlier report's Result 3 — that conversion cost is not local to the module
— **holds, and this run confirms it.** Building the whole library after variant
B surfaced one failure in a module that was not edited:

```
ForTauCeti/Analysis/Fourier/HaagerupZsido/Integrability.lean:182:2: Type mismatch
  ... has type      Integrable (fun x ↦ -Complex.I * ↑(realKernel x)) volume
      but is expected to have type   Integrable reciprocalKernel volume

Note: The following definitions were not unfolded because their definition is
not exposed:  reciprocalKernel ↦ 26
```

Lean names the cause itself. `integrable_reciprocalKernel` was stated as a term
that only typechecks if `reciprocalKernel` unfolds — exactly the pattern
`api-design` rejects: *"Do not expose bodies to compensate for missing lemmas."*

**The fix needed no new lemma.** The characteristic lemma already existed; the
consumer simply was not using it:

```lean
-- before: relies on `reciprocalKernel` unfolding
theorem integrable_reciprocalKernel : Integrable reciprocalKernel :=
  integrable_realKernel.ofReal.const_mul (-Complex.I)

-- after: goes through the characteristic lemma
theorem integrable_reciprocalKernel : Integrable reciprocalKernel := by
  rw [funext reciprocalKernel_def]
  exact integrable_realKernel.ofReal.const_mul (-Complex.I)
```

## Total cost for this module

- **1 line** — `@[expose] public section` → `public section`
- **4 characters** — `rfl` → `(rfl)` in four `_def` lemmas
- **1 theorem** — two lines to three, using a lemma that already existed

`lake build ForTauCeti` green at 8,833 jobs. **No exposure retained, no new
lemma written.**

## What this changes for the conversion

The earlier report's static count stands: **56 restatements across 31 modules**
carry a `_def`/`_apply` proved by bare `rfl`. Its conclusion does not.

- **Those 31 modules do not need `@[expose]`.** They need `(rfl)`, which is a
  mechanical substitution a script can propose and a human can eyeball.
- **The end state is nearly zero exposed bodies**, not 31 modules' worth. That
  is the difference between satisfying `api-design` and merely reducing the
  count.
- **The remaining real work is the downstream consumers** — the `.choose` /
  `.choose_spec` sites in `ResolventBound.lean` that the earlier report found,
  and the class of failure `Integrability.lean` shows. Those are genuine
  missing-lemma cases, and they are the only part that needs thought.

**Estimate revised.** The earlier report put 44% of modules at "needs
`@[expose]` on 1–4 definitions." That figure should now read: **needs `(rfl)` on
1–4 restatements, and `@[expose]` on none of them.** The unknown that remains is
unchanged and is still the only one that matters — how many downstream consumers
reach into a body, which no static scan predicts.

## Caveat, stated rather than buried

This is **one module**. It is the densest single instance of the failure
(4 of 8 observed), and the mechanism Lean reports is general — an unexposed body
is not unfolded, and `(rfl)` elaborates the restatement against the expected
type rather than by definitional unfolding. But *general mechanism* is not
*measured on 31 modules*. Each conversion group should still expect the
`Integrability.lean` class of downstream break and budget for it.
