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

**Can the four Section 2 theorems replace it?**  **Yes -- the candidate has been
built.**  `dev/palomar-candidate/` contains a compiling `Challenge.lean` with
four `[RCLike 𝕜]` headline declarations and a `Solution.lean` that discharges the
first of them from the development.

| measurement | value | policy |
| --- | --- | --- |
| `Challenge.lean` | **684 lines / 32,765 bytes** | hard 1000 / 100 KiB; preferred 300 / 32 KiB |
| imports | **1** (`import Mathlib`) | Lean core + allowlisted closure |
| local definitions | 39 | permitted, via `definition_names` |
| headline theorems | 4 | — |
| functional calculus | **none** | — |

**Correction to two earlier revisions of this report.**  The first said the
blocker was that the real angle operators cannot be named, because Mathlib has no
real continuous functional calculus for bounded operators.  The claim about
Mathlib is true; the conclusion was wrong -- `ForTauCeti` registers that
calculus.  The second then said the blocker was that the development's vocabulary
is not upstream, and that a Challenge may import only upstream.  **That does not
follow from Palomar's policy**, which permits Challenge-local definitions and
provides `definition_names` for exactly this purpose.  Both verdicts are
retracted.

What actually made the Challenge small was dropping the functional calculus from
the *statement*.  A unitarily invariant norm sees only singular values, so the
angle operators need only be named, not constructed: `sin Θ₀` is the paper's own
`(I − F₀F₀⋆)E₀`, the double-angle sines are explicit projection blocks, and the
tangents are characterised by their singular values -- which is how Davis and
Kahan introduce them.

The Challenge's unitarily invariant norm is the dimension-coherent symmetric
norming function, and `Solution.lean` proves it *is* the development's
`PaperUnitaryInvariantNorm`, by `rfl`.

---

## 7. Palomar correspondence and Solution

`dev/palomar-candidate/Solution.lean` (474 lines, no `sorry`) proves:

* the Challenge's singular values **are** the development's approximation
  numbers (`rfl`);
* a Challenge unitarily invariant norm **is** a `PaperUnitaryInvariantNorm`,
  field for field, with matching value, ideal and real norm (`rfl`);
* the Challenge's trial-residual and exact-decomposition data are the
  development's;
* the Challenge's separation is `FormBoundedSylvesterGap`, constructor by
  constructor, **including both half-infinite configurations**;
* the Challenge's reduction predicate, block, and bounded perturbation of a
  partial map are `ReducesSubspace`, `reducingRestriction` and `addBounded`;
* the Challenge's Rayleigh--Ritz data is `UnboundedRitzPair`, field for field,
  with the compression still a *partial map*;
* the Challenge's two vanishing diagonal blocks are the development's `IsOddFor`;
* the Challenge's `sin Θ` statement, from
  `sinTheta_unbounded_formGap_paperUINorm_rclike`;
* the Challenge's **ambient `sin 2Θ` clause**, from
  `sinTwoTheta_ambient_reflection_projectorDifference_paperUINorm`, at an
  *arbitrary reducing* subspace -- which is the source's own scope.

The last two hold outright at `ℂ` and at `ℝ`.

**A statement-repair pass corrected four defects in the first draft's
Challenge**, all of which would have made a proof worse than useless:

1. `tan Θ₀` was defined from the *residual* rather than from the sine of the
   principal angle;
2. the Ritz compression was forced to be bounded, losing the Appendix scope;
3. the ambient ideal-membership premise was shared with the directed clauses,
   so each directed clause carried its neighbour's hypothesis;
4. the tangents could be vacuous, and a pole read as a numerical zero.

`dev/palomar-section-two-challenge-statement-audit.md` records all four with
their dispositions, plus a clause-by-clause scope table.

The earlier claim that a *development lemma was missing* for the ambient
`sin 2Θ` clause was wrong: `ReflectionIntertwines.ofReducesSubspace` already
supplies it, and that clause is now proved.

Open, per clause: the scalar-field transport for the two capability classes; the
`sin 2Θ` directed clause at a reducing subspace with an unbounded compression;
and tangent representatives with their derived no-pole facts for `tan Θ` and
`tan 2Θ`.

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
PRODUCTION COMPLETE (one clause repaired 2026-08-31) / PALOMAR IN PROGRESS
```

All source mathematics and the 29/29 certification are complete, reviewed result
by result.

**Amended 2026-08-31.**  Section 8 of this report said the review was finished.
It was not: the Palomar statement audit, written afterwards against the printed
statements rather than against this certificate, found a defect this review had
missed.  `S2-tan-theta`'s directed clause was witnessed by theorems whose Ritz
compression is **bounded**, and the Appendix to Section 6 says of the tangent
theorem specifically that both `A₀` and `Λ₁` may be unbounded.  The certificate
could not see it because that scope atom carried no `type_requirements` -- the
only Section 2 scope atom that carried none.  Repaired by
`tanTheta_directed_unboundedRitz_paperUINorm_{complex,real}`, promoted from the
Appendix-scope Ky Fan estimates that already existed on both fields; the atom now
requires an `UnboundedRitzPair` and forbids the bounded-compression
`UnboundedTrialBlock`; regressions both ways are in the checker tests.  29/29 is
restored on the repair, not on the argument.  The lesson is recorded because it
generalizes: *a scope atom with no compiler-checkable requirement is not
certified, it is asserted.*

Palomar is **not blocked** -- that verdict, twice given and twice for a different
wrong reason, is retracted.  A four-theorem Challenge compiles inside the policy
caps with a single `import Mathlib`, and the vocabulary correspondence that was
most at risk of hiding a weakening -- the unitarily invariant norm -- holds by
`rfl`.  The first draft's four statements were *not* the paper's, and the
clause-by-clause audit that found that is now maintained alongside the candidate;
the repaired statements compile, and two of the seven printed clauses are
discharged from the development.

What is open is finishing the Solution, and it is three named pieces of
mathematics, none of them a policy or dependency obstruction:

1. **The `sin 2Θ` directed generalization**, from a spectral subspace and a
   bounded trial compression to an arbitrary reducing subspace and a partial one.
2. **The tangent correspondences** for `tan Θ` and `tan 2Θ`, with their derived
   no-pole facts.

The third — the scalar-field transport — is **done**.  `RCLike` is an open class
with exactly two models, and the two development capabilities that every generic
Section 2 statement carried as binders,
`ContinuousLinearMap.HasMinMaxLowerBoundEverywhere 𝕜` and
`ExactSinTheta.HasUnboundedSylvesterKyFan 𝕜`, are now **instances at every
`RCLike` field**, each depending only on `propext`, `Classical.choice` and
`Quot.sound`.  Three new modules carry it:

| module | carries |
| --- | --- |
| `ForTauCeti/Analysis/RCLike/ScalarTransport.lean` | `RCLikeIso`, and `ScalarTransport e E` — `E` with the induced `𝕂`-structure — with subspaces, `ᗮ`, orthogonal projections, bounded operators (function, norm, adjoint, self-adjointness), `Module.rank`, partial maps (domain, function, adjoint, self-adjointness) |
| `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/ScalarTransport.lean` | approximation numbers, linear independence, spans; the min–max instance |
| `DavisKahan/Sylvester/ScalarTransport.lean` | finite Ky Fan gauges, operator-form semibounds, the real resolvent set and spectrum, the three-constructor separation, the domain-aware Sylvester equation; the Sylvester instance |

The construction moves the scalar action and the field the inner product takes
values in and nothing else — not the vectors, the additive group, the topology or
the norm — which is exactly why ranks and singular values survive it.
Restriction of scalars (`InnerProductSpace.rclikeToReal`) would not do: over a
complex-like `𝕜` it halves the scalars, doubling `Module.rank` and changing every
approximation number.

The immediate effect on the Palomar candidate is that its two discharged
clauses, `sinTheta_proof` and `sinTwoTheta_ambient_proof`, now carry **no**
capability binders: they are the Challenge statements at an arbitrary `RCLike`
field with nothing assumed beyond the source hypotheses.

And then the Comparator layout: the candidate's `Solution.lean` imports
`Challenge`, which is right for a bridge file and wrong for a submission.  A
Comparator submission needs the Solution to redeclare the four advertised names
independently, at the same types, with real proofs.

**Nothing has been submitted to or registered with Palomar, and nothing will be
until the Comparator is green.**
