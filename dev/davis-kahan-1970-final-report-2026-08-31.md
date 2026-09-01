# Final report: ambient `sin 2Θ`, the 29-result hostile review, and Palomar

Date: 2026-08-31.  Commits: `9ccb2a8a`, `cc824790`, `8d8f2de3` (plus tally rows).
This is the report the pass brief (`goal-new.md`) asks for, in its own nine
sections.

---

## 1. Mathematical repair

### The two new theorems

```
TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_addBounded_paperUINorm_complex
TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_addBounded_paperUINorm_real
```

`DavisKahan/Sources/DavisKahan1970/SinTwoThetaAmbientUnbounded.lean`.  Their
compiler-printed types carry: an unbounded self-adjoint `A : H →ₗ.[𝕜] H`; a
bounded self-adjoint perturbation `Eop`; arbitrary measurable spectral selections
`B S : Set ℝ`; arbitrary Hilbert dimension; the whole `FormBoundedSylvesterGap`,
so the separating interval may be half-infinite; an arbitrary
`PaperUnitaryInvariantNorm`; the genuine ambient angle operator
`paperSinTwoAngleOperatorC` / `…R`; ideal membership concluded rather than
assumed; and the factor exactly `2`.  No `FiniteDimensional`, no capability
class, no implementation-only hypothesis.

### Proof route

The ambient double angle is an ambient **single** angle.
`paperSinTwoAngleOperatorC_eq_modulus_starProjection_sub` identifies
`sin 2Θ(U, V)` with `|P_{J U} − P_U|`, where `J` is the reflection through `V`,
so the theorem to apply is Proposition 6.1 on a common dense domain — which
already existed as `PaperCommonDomainSymmetricSinThetaProblem.result_every_unitarilyInvariantNorm`
and `proposition6_1_commonDomain_source_projectorDifference`.  The reflected
operator `J A J` shares `dom A`, because `V` reduces `A + H` and `H` is bounded,
so `P_V` and hence `J` preserve `dom A`.

The paper's bounded perturbation for the reflected pair is `D = H − J H J`.  Its
gauge is at most `2 N(H)` — that is where the printed factor `2` enters, and it
is the only constant in the proof.

### Transport lemmas added

| lemma | what it carries |
| --- | --- |
| `TauCeti.LinearPMap.realResolventSet_unitaryConj`, `realSpectrum_unitaryConj` | the real spectrum, as a set equality |
| `semiboundedBelow_unitaryConj_iff`, `semiboundedAbove_unitaryConj_iff` | both operator-form semibounds, in both directions |
| `reducesSubspace_unitaryConj` | the mirror of a reducing subspace reduces the conjugate |
| `reducingRestriction_unitaryConj` | the reducing restriction of the conjugate **is** the conjugate of the restriction — an equality of partial maps |
| `FormBoundedSylvesterGap.unitaryConj_left` / `.unitaryConj_right` | the source separation, casing on **every** constructor |
| `DavisKahan.addBounded_reflectionPerturbation_eq_unitaryConj` | that `A + (H − J H J)` *equals* `J A J` |
| `selfAdjointSpectralSubspace_reducing`, `selfAdjointSpectralRestriction_eq_reducingRestriction` | the complex track's bridge into theorems stated over reducing restrictions |

The first five are new reusable mathematics in
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/UnitaryTransport.lean`; the gap
transport is in `DavisKahan/Sylvester/Gap.lean`.

### Norm handling

`reflectionPerturbation_paperMem_and_gauge_le` (new) gives membership and the
factor two at an arbitrary source norm, by Fan dominance from the ideal-family
result.  Over `ℝ`, `sameSingular_paperSinTwoAngleOperatorR_reflectedProjectorDifference`
identifies `paperSinTwoAngleOperatorR U V` with the reflected projector
difference through the complexification, so the real endpoint is the
scalar-generic reflected-pair theorem at `ℝ`, not a complexification of the
complex endpoint; complexification enters only to *name* the real angle.

### Half-infinite scope

`FormBoundedSylvesterGap.unitaryConj_left`/`_right` case on `intervalExterior`,
`leftAboveRightBelow` and `leftBelowRightAbove` separately.  Nothing collapses to
the bounded interval on the way to Proposition 6.1's two crossed gaps.

---

## 2. Certificate

- **81 source clauses; 81 established; 0 open.**  The count is unchanged.
- **29 counted results; all terminal; all `PASS`.**

Every additional issue found by the result-by-result review, and its resolution:

| # | finding | kind | resolution |
| --- | --- | --- | --- |
| F1 | the ambient `sin 2Θ` clause had no witness at the row's unbounded scope | mathematical | proved (§1) |
| F2 | Corollary 4.1, Proposition 4.3, Theorem 5.2 and Theorem 6.3 are printed "for every unitary-invariant norm" but were certified at `KyFanDominantIdealFamily` | quantifier | `paperUINorm_of_kyFanDominant` + six paper-norm endpoints |
| F3 | Theorem 6.3's witnesses were existential *inside* the ideal quantifier, so the representative could vary with the ideal | quantifier | re-registered onto the parameterized paper-norm endpoints |
| F4 | the `sin 2Θ` directed clauses cited no correspondence for the reflected overlap block | registration | existing lemmas registered in `evidence.correspondence` |
| F5 | `result_conclusions` keyed on atoms of kind `theorem` alone, so five rows had a **vacuous** coverage check | checker | `CONCLUSION_ATOM_KINDS` + regression test |
| F6 | a clause's primary was not required to be canonical evidence | checker | rule + test |
| F7 | a clause's scalar field was not checked against its primary's compiler-derived one | checker | rule + test |
| F8 | the half-infinite gap justification was unchecked prose | checker | `gap_scope_hypothesis_tokens`, each required to occur in the printed type, + test |

Checked and deliberately **not** changed: Theorem 8.1 part (iii) carries
`FiniteDimensional` because that is the printed scope ("for every symmetric gauge
function `Φ` in finite dimensions"), and parts (i)–(ii) are proved without it;
Proposition 4.4 is discharged by one counterexample, which is sufficient for a
claim the source makes over either field, and the checker now records that
exemption explicitly.

Full record: `dev/davis-kahan-1970-result-semantic-review-2026-08-31.md`.

---

## 3. Previously suspicious results

| result | disposition |
| --- | --- |
| `S2-tan-theta` | unchanged.  Registration repair in the previous pass, not this one; both clauses at both fields, accepted under its documented nonlocal reading. |
| `S2-sin-two-theta` | **mathematical repair.**  Both ambient clauses were open at a bounded ambient theorem; both are now proved at the printed scope.  `SectionTwo.sinTwoTheta_ambient_complex`/`_real` bind the aliases deliberately withheld until a theorem existed. |
| `S2-tan-two-theta` | unchanged; verified.  Its directed conclusion is in the paper's own block spelling — `reflectionTangentCorner` is `J₀ tan 2Θ₀`, `paperBlockCompression Uᗮ U B` is `R` — now said so in the clause justification. |
| `DK-4.2-prop` | unchanged; the previous pass's scalar promotion holds and was re-checked. |
| `DK-8.2-thm` | unchanged; four clauses over both fields, verified against the printed statement. |

---

## 4. Checker

**Schema.**  A result declares `result_wide_scope_atoms` and one `source_clauses`
entry per printed clause per scalar field.  Each clause names one
`evidence.primary`, optional `evidence.correspondence`, its `conclusion_atoms`,
optional `clause_hypothesis_atoms`, a `scalar_scope`, a `status` and a
`justification`; an open clause must say what is missing.
`canonical_evidence[…].covers_source_atoms` is **derived** from the clauses.

**Rejects.**  The historical composition — unbounded directed theorems donating
the unbounded scope, a bounded ambient theorem donating the ambient conclusion,
union covering the row — with the diagnosis naming the offending atom and saying
"a sibling declaration may not donate this scope".

**Enforced.**  Clause primary is canonical evidence; clause scalar field equals
the primary's compiler-derived one; primary satisfies the type requirements of
its own conclusions *and* every result-wide scope atom; printed conclusions of
kind `theorem`, `lemma` or `source-assertion` are all discharged; both scalar
fields per conclusion unless a generic clause or a refutation covers it.

**Equivalent gap spellings.**  `half-infinite-gap-intervals` deliberately carries
no substring requirement — three theorem families spell it three ways, and a
wrong requirement would have rejected four correct theorems.  It instead requires
a justification *and* `gap_scope_hypothesis_tokens`, every one of which must
occur in the primary's compiler-printed type.

**Tests.**  `scripts/tests/test_davis_kahan_coherent_evidence.py`, 11 tests
(was 7).  One negative test reconstructs the old composition and asserts the
*diagnosis*; four new negative tests pin F5–F8; six positive tests pin
fixed-field siblings, separately discharged directed and ambient clauses, a
clause-local hypothesis, a correspondence chain, an open clause forcing a
nonterminal row, and the both-fields rule.

---

## 5. Section 2 API

**Fixed-field clause endpoints, all bound in `SectionTwo`:**

| result | directed | ambient |
| --- | --- | --- |
| `sin Θ` | `sinTheta_complex`, `sinTheta_real` | (single clause) |
| `tan Θ` | `tanTheta_directed_complex`, `…_real` | `tanTheta_ambient_complex`, `…_real` |
| `sin 2Θ` | `sinTwoTheta_directed_complex`, `…_real` | `sinTwoTheta_ambient_complex`, `…_real` |
| `tan 2Θ` | `tanTwoTheta_directed_complex`, `…_real` | `tanTwoTheta_ambient_complex`, `…_real` |

**Source-result certificates.**  `SectionTwo.sinTwoTheta_source_complex` and
`…_real` state both printed conclusions in one declaration: the operator, the
spectral selection and the gap are shared, and each clause's own data is
quantified inside its own conjunct, so neither clause acquires the other's
hypotheses.  `tan Θ` and `tan 2Θ` get no such certificate — their clauses share
almost no data, so a conjunction would be two disjoint theorems written next to
each other, which the clause aliases already are.

**Short names.**  `tanTheta_complex`, `sinTwoTheta_complex`,
`tanTwoTheta_complex` and their real siblings each name **one** clause.  Their
docstrings now say which and name the partner, and the implementation table lists
the clauses separately.  `SectionTwo.sinTheta` is the only bound generic short
name; the other three stay unbound.

**Capability classes.**  The four fixed-field public endpoints carry none.  The
generic `sinTheta_unbounded_formGap_paperUINorm_rclike` carries two, and they are
genuine at a field other than `ℝ` and `ℂ`.

**Why the other three generic names stay unbound.**  Recorded, with the Mathlib
API named, in `dev/section-two-rclike-endpoint-frontier.md`.  The earlier reading
— "`RCLike` is an open class, so no real/complex dispatch exists" — was wrong:
`RCLike.I_eq_zero_or_im_I_eq_one` with `realLinearIsometryEquiv` and
`complexLinearIsometryEquiv` is exactly that dispatch.  It does not unblock
anything, because the blocker is in the **statement**: the angle vocabulary and
the spectral selection live on the Hilbert space, exist over `ℂ`, and reach `ℝ`
by descent, so there is nothing to dispatch until a scalar-generic angle
vocabulary exists.  `sin Θ` is generic precisely because its conclusion is a
scalar-generic operator expression, `(I − F₀F₀⋆)E₀`.

---

## 6. Palomar Challenge

The submitted entry lives in the standalone repository
(`submodules/aiq-davis-kahan-1970-rotation-eigenvectgors-perturbation-formalization`),
which `AGENTS.md` makes its owner; this repository does not carry a second copy.
Measured there:

| | |
| --- | --- |
| path | `Challenge.lean` |
| imports | 1 (`import Mathlib`) |
| lines / bytes | 95 / 4555 |
| local definitions | 0 |
| theorems | 1 (`TauCeti.norm_starProjection_comp_starProjection_le`) |
| Solution | `Solution.lean`, 22 lines, importing the library that proves it |
| policy caps | 1000 lines / 100 KiB hard; 300 lines / 32 KiB preferred |
| dependency audit | no module of the submitted repository in the Challenge's transitive closure except the Challenge itself |

No Challenge symbol comes from DKPS-local or unmerged Tau Ceti code.

**Can the four Section 2 theorems replace it?**  Not today, and the reason is
**location, not missing mathematics**.
`dev/palomar-section-two-challenge-audit-2026-08-31.md` is the audit, against the
policy snapshot the submission repository carries, the pinned Tau Ceti
(`1b39d420…`), this workspace's Mathlib, and the operator roadmap on branch
`hilbert-space-operator-theory`.  Size is not the blocker: a Challenge measures at
roughly 350–450 lines.

Every object the four statements need exists in `ForTauCeti`.  None is upstream,
and a Challenge may import only Lean core, allowlisted Mathlib, upstream Tau Ceti
and CSLib.  Eleven of the fifteen needed concepts — approximation numbers, Ky Fan
gauges, operator ideal families, the symmetric gauge that is the paper's UI norm
class, Fan dominance, the `RCLike`-generic modulus, the ambient `sin Θ` operator,
the `LinearPMap` resolvent, the unbounded spectral PVM, the Sylvester equation —
are **already targets on the operator roadmap**.  Four are not: the real
continuous functional calculus, the unbounded spectral *subspace* and reducing
restriction, `FormBoundedSylvesterGap`, and the ambient tangent operators.

**Correction to an earlier revision of this report.**  It said the blocker was
that the real angle operators cannot be named, because Mathlib's real continuous
functional calculus for bounded operators does not exist.  The claim about
Mathlib is true; the conclusion was wrong.
`ForTauCeti/Analysis/InnerProductSpace/RealContinuousFunctionalCalculus.lean`
registers `ContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint` for every
real Hilbert space at unrestricted dimension, and `modulus` together with the
whole chain `cfc Real.sin (cfc Real.arcsin (modulus (P_U − P_V)))` elaborates
over `ℝ` directly — checked by elaborating it, not inferred.  The real angle
operators in this repository are defined by transport for historical reasons, not
because a direct definition is unavailable.

**Nothing has been submitted to or registered with Palomar.**

---

## 7. Palomar correspondence and Solution

Not built, because the Challenge it would compare against is blocked (§6).  The
existing entry's correspondence is trivial by construction: its Challenge
statement is the production declaration's own type, and its Solution imports the
module that proves it, so there is no separate vocabulary to reconcile.

The remaining Palomar policy issue is the dependency one in §6, and it is an
upstreaming problem, not a research one: land the `OperatorIdeals` and
`PolarDecomposition` roadmap topics; propose the real continuous functional
calculus (written, self-contained, and already flagged in its own docstring as a
roadmap proposal); propose the unbounded spectral subspace, the form-bounded gap
predicate and the ambient tangent operators.  All four are work this repository is
positioned to do, because it already carries the mathematics.

---

## 8. Validation

| command | result |
| --- | --- |
| `lake build` | **9712 jobs green** |
| `lake build DavisKahan.Audits.All Challenge` | **9604 jobs green**, 2 `sorry` warnings — the deliberate `Conformance` placeholders |
| `python3 scripts/check_davis_kahan_1970_result_inventory.py` | CLEAN, 29/29 terminal |
| `python3 scripts/check_davis_kahan_1970_statement_map.py` | clean |
| `python3 scripts/check_davis_kahan_1970_source_census.py` | 1161/1161 declarations resolve |
| `python3 -m unittest scripts.tests.test_davis_kahan_coherent_evidence` | 11/11 OK |
| `python3 scripts/check_declaration_name_drift.py` | OK — 12792 declarations, 0 findings |
| `aiq-lean gates run --config dev/policy/gate-suite.yaml` | **22 passed/advisory, 4 failed, 0 unavailable, 0 skipped** |

Pre-existing gate failures, at exactly their baseline counts — no regression:

| gate | count before | count after |
| --- | --- | --- |
| `check_comparator_signatures` | 10 of 45 differ | 10 of 45 differ |
| `check_tauceti_readiness` | 70 blockers | 70 blockers |
| `check_tauceti_roadmap_topics` | 69 violations | 69 violations |
| `ratchets` (`per-declaration-expose`) | 166 matches | 166 matches |

Two gates broke mid-pass and were fixed rather than baselined: docstring coverage
(two undocumented local instances, removed by consolidating them into one) and
private shadows (two private `starProjection_congr` copies, deleted in favour of
one public `Submodule.starProjection_congr` in `ForTauCeti`).  The `@[expose]` the
new module first needed was removed, so the expose ratchet did not move.

**Trust.**  `#print axioms` on all eighteen new and headline declarations —
the two ambient theorems, the two `sin 2Θ` source certificates, the Fan-dominance
bridge, the six paper-norm endpoints, the four Section 2 clause aliases, and two
transport lemmas — reports `propext, Classical.choice, Quot.sound` and nothing
else.  No `sorry`, no `admit`, no `axiom` declaration anywhere in `DavisKahan/` or
`ForTauCeti/`; the only `sorry`s in the tree are the two intentional comparator
placeholders in `Challenge/DavisKahan1970/Conformance.lean`.

---

## 9. Verdict

```
PRODUCTION COMPLETE / PALOMAR BLOCKED
```

All source mathematics and the 29/29 certification are complete, reviewed result
by result against the printed statements and against compiler-printed types.

The Palomar obstruction is external and is a **dependency-location** fact, not a
mathematical one: the four Section 2 statements need a unitarily-invariant-norm
class, infinite-dimensional approximation numbers, an `RCLike`-generic modulus,
an unbounded spectral subspace and a real continuous functional calculus, all of
which this repository has and none of which is upstream, while a Challenge may
import only upstream.  Most are already operator-roadmap targets; the audit lists
the four that are not.

The generic `[RCLike 𝕜]` surface for the other three headline results is a
narrower question than this report earlier suggested.  With the real calculus in
hand, `tan Θ`'s angle chain is writable over `𝕜` behind the same kind of
capability binder the `sin Θ` endpoint already carries, with instances at both of
the paper's fields.  What remains genuinely open is the `𝕜`-generic *spectral
selection*: the roadmap's `spectralPVM` is stated over `ℂ`, and the `ℝ` case is a
descent.
