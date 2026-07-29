# `DavisKahan/Experimental/**` sorry triage

> **Decision (owner):** a `sorry` is obsolete ONLY if nothing in the eventual complete Davis--Kahan paper could use or need it. The paper is not finished, so the 18 INVESTIGATE items are treated as **KEEP** (future paper work) unless a specific one is confirmed superseded by a sorry-free twin. Net: 0 removable today, and that is fine — the scaffolding is real.


Read-only triage of every real `sorry` proof term in the experimental tree, so a
human can prune superseded scaffolding. **No source was modified.**

Generated 2026-07-24 against the working tree (branch `main`).

## Method recap

- Enumerated `sorry` via `grep -rn` over `DavisKahan/Experimental/**/*.lean`, then
  discarded matches inside comments/docstrings and the phrases `sorry-free` / `no sorry`.
  One prose hit was dropped: `Scratch/Section7/InfiniteTanTwoThetaCore.lean:29`
  (the words "behind an axiom or `sorry`" inside a `/- -/` block).
- Enclosing declaration found by walking up to the nearest `theorem/lemma/def/instance`;
  namespace reconstructed from the `namespace`/`end` stack.
- **Production reachability**: computed the transitive `import` closure of `DavisKahan.All`
  (278 modules). The only `Experimental` module in that closure is
  `DavisKahan.Experimental.FiniteDimensional.DoubleAngle.SinTheta`, and it is **sorry-free**.
  **None** of the 8 sorry-bearing modules is reachable from production.
- **Frontier / census**: grepped each declaration name in
  `dev/davis-kahan-1970-frontier.json` (80 nodes) and
  `dev/davis-kahan-1970-full-source-census.json`.
- **Supersession**: grepped same-stem names across production (`DavisKahan/**`, `ForMathlib/**`)
  outside `Experimental/`.

## Summary counts

- **Total real sorries: 51** (across 8 modules).
- **KEEP: 33**
- **INVESTIGATE: 18**
- **REMOVE-CANDIDATE: 0**

By module role:

| role | modules | sorries | KEEP | INVESTIGATE | REMOVE |
|---|---|---|---|---|---|
| `Frontier/**` (active frontier) | Core, Section3, Section4, Section9Analytic | 29 | 29 | 0 | 0 |
| `InfiniteDimensional/**` (math-ahead scaffolding, not under `MathAhead/`) | DoubleAngle, DirectRotation, SinTheta/General, Ideals/Rectangular | 22 | 4 | 18 | 0 |
| `Scratch/**` | — | 0 | 0 | 0 | 0 |
| `MathAhead/**` | — | 0 | 0 | 0 | 0 |

No sorry lives under `Scratch/**` or `MathAhead/**`; every real sorry is either a live
frontier node or an open leaf obligation inside a live `InfiniteDimensional` module.

## Declaration table

Namespace prefix `ForMathlib.DavisKahan.Experimental.` (Frontier) or
`ForMathlib.DavisKahanExt.` (InfiniteDimensional) elided; `FN` = referenced by a
frontier node, `CN` = referenced by a census row.

| declaration | file:line | role | frontier/census | superseded-by | class | reason |
|---|---|---|---|---|---|---|
| `Frontier.SameSpectralMultiplicity` | Frontier/Core.lean:139 | Frontier | FN | — | KEEP | frontier node (foundation) |
| `Frontier.sameSpectralMultiplicity_iff_unitarilyEquivalent` | Frontier/Core.lean:149 | Frontier | FN | — | KEEP | frontier node (foundation) |
| `Frontier.Section4.proposition4_2_basisAngleSquareSum` | Frontier/Section4.lean:99 | Frontier | FN | — | KEEP | frontier node (source, Prop 4.2) |
| `Frontier.Section4.proposition4_3_squaredDisplacement_approximationNumbers` | Frontier/Section4.lean:111 | Frontier | FN | — | KEEP | frontier node (source, Prop 4.3) |
| `Frontier.Section9.RepresentsFreeBeamProblem` | Frontier/Section9Analytic.lean:63 | Frontier | FN | — | KEEP | frontier node (Sec 9 foundation) |
| `Frontier.Section9.ThirdEigenvalueIsCorrect` | Frontier/Section9Analytic.lean:68 | Frontier | FN | — | KEEP | frontier node (Sec 9 foundation) |
| `Frontier.Section9.actualSinThetaOne` | Frontier/Section9Analytic.lean:74 | Frontier | — | — | KEEP | helper def in frontier module; feeds `freeBeam_*`/`section9_*` frontier nodes |
| `Frontier.Section9.actualSinTwoThetaOne` | Frontier/Section9Analytic.lean:79 | Frontier | — | — | KEEP | helper def feeding frontier nodes |
| `Frontier.Section9.actualSinThetaSum` | Frontier/Section9Analytic.lean:84 | Frontier | — | — | KEEP | helper def feeding frontier nodes |
| `Frontier.Section9.actualSinTwoThetaSum` | Frontier/Section9Analytic.lean:89 | Frontier | — | — | KEEP | helper def feeding frontier nodes |
| `Frontier.Section9.actualTanThetaOne` | Frontier/Section9Analytic.lean:94 | Frontier | — | — | KEEP | helper def feeding frontier nodes |
| `Frontier.Section9.actualTanThetaSum` | Frontier/Section9Analytic.lean:99 | Frontier | — | — | KEEP | helper def feeding frontier nodes |
| `Frontier.Section9.actualTanTwoThetaOne` | Frontier/Section9Analytic.lean:104 | Frontier | — | — | KEEP | helper def feeding frontier nodes |
| `Frontier.Section9.actualTanTwoThetaSum` | Frontier/Section9Analytic.lean:109 | Frontier | — | — | KEEP | helper def feeding frontier nodes |
| `Frontier.Section9.freeBeamClosedFourthDerivative` | Frontier/Section9Analytic.lean:114 | Frontier | FN (×2) | — | KEEP | frontier node (foundation) |
| `Frontier.Section9.freeBeamClosedFourthDerivative_isSelfAdjoint` | Frontier/Section9Analytic.lean:119 | Frontier | — | — | KEEP | supports `freeBeamClosedFourthDerivative` frontier node |
| `Frontier.Section9.canonicalFreeBeamAnalyticModel` | Frontier/Section9Analytic.lean:125 | Frontier | FN | — | KEEP | frontier node (bridge) |
| `Frontier.Section9.canonicalFreeBeamAnalyticModel_representsSource` | Frontier/Section9Analytic.lean:133 | Frontier | — | — | KEEP | supports `canonicalFreeBeamAnalyticModel` frontier node |
| `Frontier.Section9.freeBeam_thirdEigenvalue_gt_fiveHundred` | Frontier/Section9Analytic.lean:141 | Frontier | FN | — | KEEP | frontier node (source) |
| `Frontier.Section9.freeBeam_exact_finite_data` | Frontier/Section9Analytic.lean:151 | Frontier | FN | — | KEEP | frontier node (bridge) |
| `Frontier.Section9.freeBeamFiniteDataCertificate_of_model` | Frontier/Section9Analytic.lean:160 | Frontier | — | — | KEEP | supports `freeBeam_exact_finite_data` frontier node |
| `Frontier.Section9.section9_initial_angle_bounds` | Frontier/Section9Analytic.lean:171 | Frontier | FN | — | KEEP | frontier node (source) |
| `Frontier.Section9.section9_tangent_angle_bounds` | Frontier/Section9Analytic.lean:182 | Frontier | FN | — | KEEP | frontier node (source) |
| `Frontier.Section9.theoremOutputCertificate_of_model` | Frontier/Section9Analytic.lean:192 | Frontier | — | — | KEEP | supports the `section9_*` frontier nodes |
| `Frontier.Section9.section9_numericalExampleCertificate` | Frontier/Section9Analytic.lean:199 | Frontier | FN | — | KEEP | frontier node (source) |
| `Frontier.Section3.twoProjection_operator_classification` | Frontier/Section3.lean:1036 | Frontier | FN | — | KEEP | frontier node (bridge, Thm 3.1) |
| `Frontier.Section3.theorem3_1_spectralMultiplicity_classification` | Frontier/Section3.lean:1047 | Frontier | FN | — | KEEP | frontier node (source, Thm 3.1) |
| `Frontier.Section3.compactAngleEigenvalueList` | Frontier/Section3.lean:1055 | Frontier | FN | — | KEEP | frontier node (foundation) |
| `Frontier.Section3.corollary3_1_compact_angleList_classification` | Frontier/Section3.lean:1068 | Frontier | FN | — | KEEP | frontier node (source, Cor 3.1) |
| `RectangularSymmetricIdealFamily.compactOperatorNorm` | InfiniteDimensional/Ideals/Rectangular.lean:41 | InfDim | — | — | KEEP | memory-designated active ideal-family frontier; open leaf "handed to math agent"; live importers (see caveat) |
| `RectangularSymmetricIdealFamily.hilbertSchmidt` | InfiniteDimensional/Ideals/Rectangular.lean:56 | InfDim | — | — | KEEP | active ideal-family frontier; open analytic campaign |
| `RectangularSymmetricIdealFamily.traceClass` | InfiniteDimensional/Ideals/Rectangular.lean:70 | InfDim | — | — | KEEP | active ideal-family frontier; open analytic campaign |
| `RectangularSymmetricIdealFamily.schatten` | InfiniteDimensional/Ideals/Rectangular.lean:83 | InfDim | — | — | KEEP | active ideal-family frontier; open analytic campaign |
| `SymmetricNormIdeal.sinAngle_reflected_mem_gauge_eq` | InfiniteDimensional/DoubleAngle.lean:605 | InfDim | — | partial (norm-only) | INVESTIGATE | `DoubleAngleGenuine` proves the operator-**norm** twin (`subspaceGap_map_reflection_eq_norm_sinTwoAngle`) but NOT the symmetric-norm-ideal gauge/membership statement; not superseded |
| `operatorAbsoluteValue_sq` | InfiniteDimensional/DirectRotation.lean:74 | InfDim | — | — | INVESTIGATE | tagged "leaf obligation"; not in frontier/census; no sorry-free twin; imported by live `Core/Unbounded`, `SpectraBridge/DirectRotationAPI` |
| `operatorAbsoluteValue_isSelfAdjoint` | InfiniteDimensional/DirectRotation.lean:79 | InfDim | — | — | INVESTIGATE | leaf obligation, live importers |
| `canonicalIntertwinerUnit` | InfiniteDimensional/DirectRotation.lean:86 | InfDim | — | — | INVESTIGATE | leaf obligation, live importers |
| `coe_canonicalIntertwinerUnit` | InfiniteDimensional/DirectRotation.lean:95 | InfDim | — | — | INVESTIGATE | leaf obligation, live importers |
| `canonicalAbsoluteValueUnit` | InfiniteDimensional/DirectRotation.lean:102 | InfDim | — | — | INVESTIGATE | leaf obligation, live importers |
| `coe_canonicalAbsoluteValueUnit` | InfiniteDimensional/DirectRotation.lean:111 | InfDim | — | — | INVESTIGATE | leaf obligation, live importers |
| `canonicalAbsoluteValue_commutes_projection` | InfiniteDimensional/DirectRotation.lean:120 | InfDim | — | — | INVESTIGATE | leaf obligation, live importers |
| `directRotation_sq` | InfiniteDimensional/DirectRotation.lean:385 | InfDim | census refs finite-dim twin only | fin-dim twin (different statement) | INVESTIGATE | census `directRotation_sq` points at `DavisKahanTheory.directRotation_sq` (finite-dim, `FiniteDimensional/DirectRotation/Basic.lean`); this infinite-dim `DavisKahanExt` version is not that node |
| `directRotation_minimal` | InfiniteDimensional/DirectRotation.lean:423 | InfDim | — | — | INVESTIGATE | leaf obligation, live importers |
| `norm_sylvester_le_of_orderedSeparation_rclike` | InfiniteDimensional/SinTheta/General.lean:58 | InfDim | — | ℂ-case only | INVESTIGATE | tagged leaf; ℂ case done in `Sylvester/Basic`; general `RCLike` transport open; module imported by live `DoubleAngle`, `SinTheta/All` |
| `norm_sylvester_le_of_generalSeparation_rclike` | InfiniteDimensional/SinTheta/General.lean:71 | InfDim | — | ℂ-case only | INVESTIGATE | tagged leaf; ℂ case done in `Sylvester/Basic`; general `RCLike` transport open |
| `spectralSubspace` | InfiniteDimensional/SinTheta/General.lean:467 | InfDim | — | — | INVESTIGATE | open def; live importers; finite-dim namesakes exist but different type |
| `spectralSubspace_hasOrthogonalProjection` | InfiniteDimensional/SinTheta/General.lean:474 | InfDim | — | — | INVESTIGATE | instance on the above open def |
| `reduces_spectralSubspace` | InfiniteDimensional/SinTheta/General.lean:487 | InfDim | — | fin-dim namesakes | INVESTIGATE | name also in `FiniteDimensional/**`, `Specialized/**` but those are finite-dim twins, not this general version |
| `operatorAbsoluteValue` | InfiniteDimensional/SinTheta/General.lean:551 | InfDim | — | — | INVESTIGATE | open def underpinning DirectRotation leaves |
| `SymmetricNormIdeal.operatorAbsoluteValue_mem_and_gauge_eq` | InfiniteDimensional/SinTheta/General.lean:566 | InfDim | — | — | INVESTIGATE | leaf obligation, live importers |
| `projectionDifference_ideal_intervalExterior` | InfiniteDimensional/SinTheta/General.lean:588 | InfDim | — | — | INVESTIGATE | leaf obligation, live importers |

## Safe to delete now

**None.** No module qualifies. Every sorry-bearing module is imported by at least one
other live `Experimental` module (though none by production), and no module has all of
its sorries classified REMOVE-CANDIDATE. Concretely:

- `Frontier/{Core,Section3,Section4,Section9Analytic}` — all sorries are tracked frontier
  nodes; imported by `Frontier/All`, `Frontier/Lemma63`, `Frontier/RieszCircle`,
  `MathAhead/Section3Elementary`, `MathAhead/HiddenFoundations/HalmosClassification`.
- `InfiniteDimensional/{DoubleAngle,DirectRotation,SinTheta/General,Ideals/Rectangular}` —
  imported by live siblings (`DoubleAngleGenuine`, `Frontier/Section3`, `Core/Unbounded`,
  `SpectraBridge/DirectRotationAPI`, `SinTheta/ContinuationCore`, `SinTheta/RestrictionCompat`,
  `Ideals/Symmetric`, `Scratch/SharedFoundations/Ideal/ReflectionTransport`, ...).

So there is nothing this pass can confidently recommend deleting. The pruning value here is
the INVESTIGATE list, not a delete list.

## Caveats / could-not-determine

1. **No REMOVE-CANDIDATE found, by design of the conservative rule.** There are zero
   sorries under `Scratch/**` or `MathAhead/**`, and I found no confirmed sorry-free twin
   proving the same-or-stronger statement for any InfiniteDimensional sorry. The classic
   prune targets (superseded Scratch sketches) simply do not have live `sorry` terms right
   now — those trees are already clean.
2. **`Ideals/Rectangular` (4 sorries) classified KEEP on memory, not on JSON.** The four
   family constructors (`compactOperatorNorm`, `hilbertSchmidt`, `traceClass`, `schatten`)
   are **not** frontier nodes or census rows, but auto-memory
   (`unbounded-sin-theta-capstone-compiled`: "ideal-family instances are the frontier") and
   the in-file docstrings ("open obligation ... handed to the mathematics agent") mark them
   as the active analytic frontier. If that memory is stale, these would drop to INVESTIGATE.
   They are genuinely open (Schauder/HS/trace-class/Schatten over `RCLike` absent from pinned
   Mathlib), so they are certainly not deletable, only possibly re-labelable.
3. **The 18 InfiniteDimensional INVESTIGATE sorries are "math-ahead" scaffolding that is not
   tracked by the frontier JSON.** They are all tagged "**Leaf obligation**" in-source and are
   imported by live experimental modules, but the frontier tracker does not currently point at
   them. Whether they are (a) genuine future work the tracker simply omits, or (b) obsolete
   scaffolding kept alive only by equally-obsolete importers, cannot be settled from the import
   graph + JSON alone — it needs a human/math judgment about the InfiniteDimensional program's
   status. Memory hints both ways: the unbounded sin-Θ chain is reportedly "axiom-clean /
   compiled", which suggests the production-facing results route *around* these leaves, yet the
   files remain in the build.
4. **`DoubleAngle.lean:605` (`sinAngle_reflected_mem_gauge_eq`) is partially superseded.**
   `DoubleAngleGenuine.lean` proves the operator-**norm** reflection identity sorry-free, but
   the open sorry is the stronger **symmetric-norm-ideal gauge + membership** equality, which
   `DoubleAngleGenuine` does not establish. Left INVESTIGATE, not REMOVE.
5. **Frontier node `status`/`sorry_count` fields are absent** in `davis-kahan-1970-frontier.json`
   (all `status = null`), so "frontier-referenced" was determined by declaration match only, not
   by an explicit open/closed flag. Every Frontier sorry decl does match a node, so KEEP is safe
   regardless.
6. I did **not** run a full `lake build`; reachability is from static `import`-graph parsing of
   `DavisKahan/**` only (`ForMathlib`/`Mathlib`/`Spectra` imports were followed by name but those
   trees were not walked for further edges — irrelevant here since no sorry module is in the
   production closure anyway).

## Definitional holes dominate, and they have dependents (edward/fable, 2026-07-29)

Measured across `DavisKahan/**` excluding `vendor/` and `external/`:
**31 `sorry`ed *definitions*** against **70 `sorry`ed theorems**.

That ratio matters more than either number. A `sorry`ed theorem is an honest
debt: the statement is meaningful and someone can prove it. A `sorry`ed
*definition* is worse in kind — `sorryAx` makes the body opaque, so **every
theorem stated about it asserts nothing checkable**, whether proved or not.

### Two holes carry nine declarations between them

| hole | dependent `sorry`s | what they are |
|---|---:|---|
| `operatorAbsoluteValue` (`SinTheta/General.lean:550`) | **5** | `operatorAbsoluteValue_sq`, `operatorAbsoluteValue_isSelfAdjoint`, `coe_canonicalAbsoluteValueUnit`, `canonicalAbsoluteValue_commutes_projection`, `SymmetricNormIdeal.operatorAbsoluteValue_mem_and_gauge_eq` |
| `spectralSubspace` (same file) | **2** | `spectralSubspace_hasOrthogonalProjection`, `reduces_spectralSubspace` |

None of those seven is independently workable. They are not seven open
problems; they are **two**, plus seven consequences that become attemptable the
moment the definitions are real.

`operatorAbsoluteValue`'s blocker is recorded in `dev/LANES.md` and is
**upstream**: the file is `RCLike`-general, `ContinuousLinearMap.modulus` is
ℂ-only, `LinearMap.IsPositive.sqrt` is finite-dimensional only, and
`PositiveSqrt.lean`'s own header names the cause — the C⋆-algebra/CFC instances
on `E →L[𝕜] E` are registered only for `𝕜 = ℂ`.

### Why this is worth stating

Effort estimates built from `sorry` counts overstate this development's
remaining work, because the counts treat consequences as independent problems.
The honest reading of `SinTheta/General.lean` is **one scope decision** —
restrict to `ℂ` and use `modulus`, or wait for an `RCLike` CFC — after which
seven obligations become ordinary proof work.

Corollary for anyone triaging: **check whether a `sorry` is a definition before
estimating it**, and if it is, count its dependents before treating them as
separate lanes.


## Gate audit: which measuring instruments can be trusted (edward/fable, 2026-07-29)

Three separate instruments were found wrong in one session, and in **every case
the error pointed toward "looks fine"**:

| instrument | defect | what it reported |
|---|---|---|
| `check_davis_kahan_frontier.py` Lean probe | three stacked causes (orphan `.olean`s, a root that did not compile, pre-Wave-1 `ForMathlib.*` names) | `status unknown` — for as long as anyone had looked |
| `check_docstring_coverage.py` | `DECL` anchored the keyword after *modifiers*; an attribute bracket is not a modifier, so `@[simp] theorem foo` was **skipped entirely** | `OK` over **158** undocumented declarations |
| an ad-hoc `finddoc` scan (mine) | did not strip comment interiors | inflated `ForTauCeti` roughly 2× and produced four prose false positives |

All three are fixed. Because the pattern is a *parser* problem rather than three
unrelated bugs, the remaining gates were audited on the same axis:

* **`check_declaration_name_drift.py` — clean, and verified empirically, not by
  reading the regex.** Its `_MODIFIERS` opens with `(?:@\[[^\]]*\]\s*)*`, so
  inline attributes are matched; `@[simp] theorem foo`, `@[simp, norm_cast]
  noncomputable def baz` and the plain form all resolve to the right name. This
  matters more than the others: name-drift is what protects renames, so a blind
  spot there would let a rename of any `@[simp]` lemma pass unnoticed.
* **`check_library_structure.py` — not exposed.** It parses *imports* and scans
  for `sorry`/`admit` on comment-stripped text; it never parses declarations, so
  the axis does not apply. Its `load()` does strip block and line comments
  correctly (checked when I wrongly accused it of the opposite).
* **`check_dependency_layers.py` — not exposed**, same reason.

**The generalisable rule.** Every one of these gates parses Lean with regexes,
and every failure was on the same question: *what counts as the start of a
declaration?* Attributes, block comments, `omit`/`set_option` lines between a
docstring and its declaration, and `end`/`section` on consecutive lines have each
broken a scanner here. When adding a gate, test it against those four shapes
before trusting a green result — and prefer a green result you have tried to
falsify over one you have merely observed.
