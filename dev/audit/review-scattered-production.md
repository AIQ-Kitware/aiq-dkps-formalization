# Review — the 19 scattered production modules

**Status: COMPLETE for the 19 Lean files.** Written 2026-07-31 by
`edward (aiq-gpu-docs)`, lane `AUDIT`, cluster (iv) of the 50-file tail.

Unlike the other clusters these share no subject; they are what was left when
`ApproximationNumber/` and `Sources/DavisKahan1970/` were taken as groups. Three
of them (`EnergyComparison`, `Schatten`, `ENNRealLiminf`) I wrote earlier today,
and that is stated rather than hidden — see *Method* below.

Reviewed:

- [x] `DavisKahan/DoubleAngle/CompatibilitySinTwoTheta.lean` (54 lines, 2 decls)
- [x] `DavisKahan/Experimental/InfiniteDimensional/DoubleAngleSpectrum.lean` (570, 25)
- [x] `DavisKahan/Experimental/InfiniteDimensional/SinTheta/BoundedBorelProjectionComplex.lean` (83, 2)
- [x] `DavisKahan/OperatorIdeal/Majorization/All.lean` (9, 0 — aggregate)
- [x] `DavisKahan/OperatorIdeal/Majorization/WeakSubmajorization.lean` (139, 11)
- [x] `DavisKahan/SinTheta/Natural/SpectralSubspace.lean` (153, 3)
- [x] `DavisKahan/SpectralTheory/Complexification/Spectrum.lean` (127, 8)
- [x] `DavisKahan/SpectralTheory/ContinuationContour.lean` (205, 15)
- [x] `DavisKahan/SpectralTheory/ContinuationRieszIntegral.lean` (274, 18)
- [x] `DavisKahan/Sylvester/FiniteBlockReconstruction.lean` (355, 10)
- [x] `DavisKahan/Sylvester/OrthogonalIdempotentExp.lean` (202, 4)
- [x] `ForTauCeti/Analysis/InnerProductSpace/Complexification/Basic.lean` (622, 70)
- [x] `ForTauCeti/Analysis/InnerProductSpace/Complexification/FunctionalCalculus.lean` (454, 31)
- [x] `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SubmoduleAdjoint.lean` (177, 4)
- [x] `ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Subspace.lean` (129, 8)
- [x] `ForTauCeti/Analysis/InnerProductSpace/SpectralOrder/Real.lean` (284, 5)
- [x] `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/EnergyComparison.lean` (660, 23)
- [x] `ForTauCeti/Analysis/OperatorIdeal/Family/Schatten.lean` (526, 22)
- [x] `ForTauCeti/Topology/ENNRealLiminf.lean` (89, 1)

## Finding SC-1 — a completed proof documented as a plan to prove it `{lane:AUDIT}`

`ForTauCeti/Analysis/InnerProductSpace/SpectralOrder/Real.lean` is **five proved
theorems, no `sorry`, no axiom, assigned to topic T17 on the submission ladder.**
Its prose, in full, described work that had not been done:

* the module heading was *"# Real spectral bridge **roadmap**"*;
* the docstring said it *"records the **missing** real-Hilbert-space bridge"* and
  that *"the declarations here are **excluded from the supported umbrella until
  the bridge is discharged**"*;
* a **70-line section headed `## Weak-agent execution plan`** instructed a future
  implementer not to attempt the theorem by rewriting complex CFC results, and
  laid out a "preferred route" (build a complexification) and an "alternative
  route" (construct the real CFC instance) with numbered sub-steps;
* the bridge theorem's own docstring opened *"This is the one genuinely missing
  theorem in the real bridge"*, followed by *"Implementation strategy: …"*;
* the final theorem — the **sharp real Davis–Kahan bound**, the paper's headline
  result in the real case — was labelled *"**Target** sharp real Davis–Kahan
  theorem"*.

**The bridge is proved.** `upperFormBoundOn_top_of_spectrum_subset_Iic` runs the
Rayleigh shift — `set m := ‖A‖ + 1`, `set S := A + algebraMap ℝ _ m` — which is
the route the plan section listed as *neither* of its two options, and the last
theorem discharges to `Submodule.opNorm_starProjection_sub_le_of_formBounds`.

This is the third instance today of the same defect and the most severe, so the
judgement recorded in `review-approximation-number.md` — that finding AN-1 was
*"a single instance, not a pattern, and no gate is warranted"* — **is superseded
by this file.** The three:

| | file | claim | reality |
|---|---|---|---|
| AN-1 | `ApproximationNumber/Core.lean` | namespace "is still" the staging one | it is `TauCeti.ApproximationNumber` |
| AN-2 | same | points at module `ApproximationNumbers` | no such module in this library |
| SC-1 | `SpectralOrder/Real.lean` | roadmap, bridge missing, results excluded | five theorems, on the ladder |

A reviewer meeting SC-1 concludes that five theorems on the submission path are
unsupported placeholders and that the real Davis–Kahan theorem is future work.
**It is the opposite of a `sorry`: the mathematics is there and the prose says it
is not**, which no escape-counting gate can see — `check_tauceti_readiness`
reports this module at 0 proof escapes, correctly.

Rewritten: the module docstring now states what is proved and keeps the one piece
of the plan that was real mathematical content — *why* a norm bound `‖A‖ ≤ c`
cannot replace the argument, namely that `spectralRadius` records absolute values
so the positivity of the shifted spectrum has to be used before the supremum
becomes the endpoint. The two mislabelled theorem docstrings now say what their
theorems prove. `lake build` green; `check_submission_prose`,
`check_docstring_coverage` and `check_tauceti_readiness` all pass.

**Measured after fixing, to size the pattern rather than assume it:** across all
of `ForTauCeti/**`, occurrences of `execution plan`, `weak-agent`, a `roadmap`
heading, `Target` opening a docstring, `should be proved/added`, and `TODO` are
now **zero**. So the pattern was real but confined, and a gate would have one
historical hit and no future one. Recorded, not gated — same conclusion as AN-1,
now reached from three data points instead of one.

## No finding

**Mechanically clean across all nineteen**: no `sorry`, no `TODO`, no primed
name, no proof over 90 lines, and `generate_all_aggregates.py --check` reports
`aggregates up to date`, which covers `Majorization/All.lean` — a 9-line
aggregate whose one import is the directory's one module.

Every backticked dotted reference in all nineteen resolves. Two that looked
wrong are not: `SpectralOrder/Real.lean` cites
`TauCeti.DavisKahan.Experimental.Foundation.RealSpectralBridge` inside a
*provenance* line recording what the namespace **became**, which is the correct
use of a dead name; and `SubmoduleAdjoint.lean` cites
`LinearPMap.adjoint_graph_eq_graph_adjoint`, which is Mathlib's, in
`Mathlib/Analysis/InnerProductSpace/LinearPMap.lean`.

`DavisKahan/Sylvester/{OrthogonalIdempotentExp,FiniteBlockReconstruction}.lean`
and `DavisKahan/SpectralTheory/Continuation{Contour,RieszIntegral}.lean` are the
four promoted under `{lane:EXP-PROMOTE-MISC}` and `{lane:EXP-PROMOTE-SYL}`, and
their provenance blocks are the model for what a promotion note should say —
`OrthogonalIdempotentExp` records that *"it became promotable because
`Sylvester/FiniteStepCalculus.lean` was promoted an hour earlier … that was its
only Experimental import, so clearing one module cleared this one"*, which is the
cascade `{lane:EXP-PROMOTE-SIZING}` predicted, written down where the next
promoter will find it.

`Complexification/Basic.lean` is 70 declarations in 622 lines with no proof over
23 — the highest declaration density in the group and exactly what a transport
layer should look like.

`DavisKahan/SinTheta/Natural/SpectralSubspace.lean` is the one file here that
`namespace`s into `TauCeti.DavisKahan.Experimental.ExactSinTheta`. It is one of
the 101 counted in finding S-4 of `review-sources-1970-sharp.md` and needs no
separate treatment.

## Method, stated because three of these are mine

`EnergyComparison.lean`, `Schatten.lean` and `ENNRealLiminf.lean` were written by
this same agent earlier today. **A self-review is worth less than a review**, and
the honest form is to say what it consisted of rather than to tick quietly: for
those three, the structural measurements and the cross-reference check were run
identically, but the reading was a re-reading, and the useful check on them was
the one already applied at the time — `audit_scan --dup`, which found the two
independently-drafted duplicates that split `Schatten.lean` in the first place.
Whoever next takes lane `AUDIT` should treat those three ticks as weaker than the
other sixteen.
