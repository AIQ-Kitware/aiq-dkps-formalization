# What converting `ForTauCeti` off blanket `@[expose]` actually costs

**Lane `FTC-EXPOSE-MEASURE`, run 2026-07-30 by `jon (yardrat)`.** Jon adopted Tau
Ceti's `api-design` rubric over this repository's former house rule the same day:
bodies stay hidden, `@[expose]` goes on the individual declarations a consumer must
unfold, and the docstring says why. 70 of 167 modules currently open
`@[expose] public section`.

The lane's question was *what fraction breaks, and what replaces each break*. The
method was the one the row prescribes: strip the blanket from a sample, build, and
record for each failure which declaration needed unfolding.

**Nothing in this document is a conversion.** The sample was restored; the tree is
unchanged and `check_expose_ratchet.py` reads 70 of 167.

## The sample

Seven modules spanning the shapes, chosen before the build was run:

| module | shape |
|---|---|
| `Analysis/Fourier/HaagerupZsido/Defs.lean` | definition-heavy |
| `Analysis/InnerProductSpace/LinearPMap/Resolvent.lean` | `LinearPMap` |
| `Analysis/OperatorIdeal/ApproximationNumber/Basic.lean` | `OperatorIdeal` |
| `Analysis/InnerProductSpace/ProjValMeasure/Basic.lean` | structure-carrying |
| `Analysis/Fourier/ExponentialAbs.lean` | scalar analysis, theorem-only |
| `MeasureTheory/CompactExists.lean` | `MeasureTheory`, theorem-only |
| `Analysis/InnerProductSpace/BorelCalculus/PVM.lean` | derived structure |

Two further candidates (`HilbertSchmidtPythagoras.lean`, `HilbertSchmidtLp.lean`)
turned out **not** to carry the blanket at all, which is itself worth knowing: the
rule was never quite universal.

## Result 1 — three of seven convert for free

`ExponentialAbs.lean`, `CompactExists.lean` and `ProjValMeasure/Basic.lean` built
with no error at all. **The structure-carrying module is among them**, which
contradicts the natural guess that a structure needs its body exposed: its
extensionality lemmas (`ext_of_diag`, `ext_iff_proj`) are already stated, so no
consumer reaches for the fields.

That is the shape to look for when scoping a slice: *a module whose characteristic
lemmas already exist converts free.*

## Result 2 — the other four fail identically, and the fix is mechanical

Every failure in the sample modules themselves was the same:

```
error: …/Defs.lean:36:0: Not a definitional equality: the left-hand side
```

on a `*_def` restatement proved by bare `rfl` — `weight_def`,
`weightLaplaceTransform_def`, `realKernel_def`, `reciprocalKernel_def`,
`approximationNumber_eq_iInf`, `spectrum_eq_compl`, `toProjValMeasure_proj`,
`toProjValMeasure_diag`. **Eight failures, eight `rfl` lemmas, in four files.**

These are not the rubric's *missing lemma* case: the characteristic lemma already
exists — it *is* the thing that broke. A `foo_def` lemma is by definition a
consumer that must unfold, so `@[expose]` on `foo` is the rubric's own carve-out,
and the conversion is: **blanket out, `@[expose]` on the handful of definitions
that carry a `_def`/`_apply` restatement.** In this sample that was 1–4
definitions per file.

## Result 3 — the cost is not bounded by the file, and this changes the plan

Applying result 2 to the four files did **not** make the build green. It moved the
failure downstream, to modules that were not in the sample:

```
error: …/LinearPMap/ResolventBound.lean:66:5: Invalid field `choose`:
       the environment does not contain `TauCeti.LinearPMap.resolventSet.choose`
```

`ResolventBound.lean` projects `.choose` and `.choose_spec` out of the definitional
`∃` in `resolventSet` — four sites. That is the rubric's *real* target: a consumer
reaching into a body because the lemma that should hand it the data was never
written. The replacement is a characteristic lemma along the lines of
`exists_resolvent_of_mem_resolventSet`, returning the operator and its two
inverse properties.

Exposing `resolventSet` to get past it moved the failure again, to
`SpectralMeasure/Construction.lean`, which `rw`s with `specProjection`,
`spectralPVM` and `toProjValMeasure_proj` — i.e. rewrites *by definition name*
across a module boundary.

**So a module's conversion cost is not local to the module.** The unit is a
dependency-closed group, and the sample's `LinearPMap` file dragged in at least two
modules outside its own directory.

## The estimate the lane asked for

Of 70 modules, extrapolating from a 7-module sample — stated as an estimate, not a
measurement, because only 7 were tried:

- **~56% (39 of 70)** are candidates for a free conversion: theorem-only modules
  and modules whose characteristic lemmas are already complete.
- **44% (31 of 70)** need `@[expose]` on 1–4 named definitions. This one is not an
  extrapolation — it is a static count, given below: **the definitions that carry a
  `_def` or `_apply` lemma proved by bare `rfl`**. The 7-module sample ran 4 of 7,
  which is consistent with it.
- **An unknown but non-zero number** additionally need a *new* characteristic
  lemma, because a consumer projects out of a body (`.choose` on a definitional
  `∃` is the observed instance). These are the only ones that are real work, and
  they cannot be found without building.

## The recommendation, and it contradicts the current slice scoping

`FTC-EXPOSE-a` … `-e` are scoped **by directory**. Result 3 says that is the wrong
axis: `LinearPMap/Resolvent.lean` (slice b) cannot be converted without touching
`ResolventBound.lean` (slice b) *and* `SpectralMeasure/Construction.lean` (slice b)
— that one happens to stay inside b, but `BorelCalculus/PVM.lean` (slice c) is
rewritten by name from `LinearPMap/SpectralMeasure/Construction.lean` (slice b), so
b and c collide.

Two ways to fix the scoping, and the choice belongs to whoever owns the chain:

1. **Re-slice along the import graph** rather than the directory tree, so each
   slice is dependency-closed. `scripts/derive_tauceti_submission_ladder.py`
   already computes closures and could be reused.
2. **Keep the directory slices but land them in one commit each with a shared
   ratchet**, accepting that a slice may have to touch a file another slice owns —
   which is exactly the collision `dev/LANES.md` exists to prevent, so this is the
   worse option.

**A cheap first step either way**: list the definitions carrying a bare-`rfl`
`_def`/`_apply` lemma. That set is computable statically, it is the bulk of the
work, and having it turns each slice from an exploration into an edit.

**Done — here is the list, measured the same day.** Scanning `ForTauCeti/**` for a
`theorem …_def` / `…_apply` (and the two irregular names the sample turned up)
whose proof is a bare `rfl`:

**56 restatements across 31 modules.** The heaviest, which are the files a
conversion slice should budget for:

| count | module | lemmas |
|---|---|---|
| 5 | `LinearPMap/SpectralMeasure/Construction.lean` | `cayleyCoord_apply`, `cayleyDenomCM_apply`, `resolventSymbol_apply`, `cayleyDenomInvCM_apply`, … |
| 4 | `Fourier/HaagerupZsido/Defs.lean` | the four kernel `_def`s |
| 4 | `RectangularUnitarilyInvariantNorm/Instances.lean` | `opNorm_apply`, `kyFan_apply`, `nuclear_apply`, `toRectangular_apply` |
| 3 | `LinearPMap/Constructions.lean` | `perturb_apply`, `boundedPerturbation_apply`, `unitaryConj_apply` |
| 3 | `…ReciprocalMultiplier/OrbitAction.lean` | `unitaryOrbitAction_apply`, `doubledRealRotation_apply`, `doubledComplexScalarAction_apply` |

The remaining 26 modules carry one or two each. **31 of the 70 blanket modules are
therefore known in advance to need at least one `@[expose]`**, and the other 39 are
candidates for a free conversion — subject to result 3, which is the part no static
scan can predict.

Reproduce with a scan for `theorem …_def|…_apply` followed within twelve lines by
`:= rfl`; the exact script is short enough to inline in whichever slice takes it
first.
