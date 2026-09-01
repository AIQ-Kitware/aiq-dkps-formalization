# Davis--Kahan 1970: hostile result-by-result semantic review, 2026-08-31

This is a full re-review of all 29 counted results, performed after the
coherent-clause certificate was introduced (8499471d) and after the ambient
`sin 2Theta` theorem was proved at the source's unbounded scope.  It supersedes
the 2026-08-12 sweep as the current review of record; that report remains
accurate about the state it describes and is kept as history.

## Why it was redone

The 2026-08-12 sweep accepted a certificate assembled by taking the **union**, per
result, of the source atoms its canonical declarations covered.  That accepts a
conjunction no theorem proves, and it did: `S2-sin-two-theta`'s unbounded
directed endpoints donated the unbounded scope while a **bounded** ambient theorem
donated the ambient conclusion.  The clause model replaced the union; this review
is the semantic pass that the mechanical model cannot do for itself.

## Method

For each result: read the printed statement in the checked-in distributable
specification, enumerate its separately quantified clauses, then read the
**compiler-printed type** of each clause's canonical witness -- not its name --
and compare, axis by axis: scalar field, bounded/unbounded operator scope, domain
assumptions, dimension, norm class, separation alternatives, residual versus
ambient perturbation, directed versus ambient angle, constants, representative
choice, and any hypothesis present in Lean but not in the paper (or the reverse).

The eight patterns searched for by name were: a bounded theorem donating a
conclusion to an unbounded row; a finite-dimensional theorem donating to an
infinite-dimensional row; an operator-norm or ideal-family theorem donating to an
arbitrary-unitarily-invariant-norm row; one scalar field canonical while the other
is merely supporting; directed and ambient quantities conflated; source gap
alternatives split across incompatible witnesses; a source hypothesis dropped;
an implementation-only hypothesis added.

## What the review found

Eight findings, all repaired in this pass.  Four are mathematical or
registration defects in the certificate; four are holes in the checker that
allowed a defect of that kind to pass unnoticed.

### Mathematical and registration findings

**F1 — `S2-sin-two-theta`, ambient clause, both fields.**  The printed ambient
conclusion `delta ||sin 2Theta|| <= 2 ||H||` had no witness at the row's own
unbounded scope; the only paper-norm ambient endpoints took bounded ambient
operators.  *Repaired* by
`sinTwoTheta_ambient_unbounded_addBounded_paperUINorm_complex` and its real
sibling, proved in this pass.  This is a mathematical repair, not a registration
repair.

**F2 — four results certified at an ideal family, not at the paper's norm.**
Corollary 4.1, Proposition 4.3, Theorem 5.2 and Theorem 6.3 are printed "for
every unitary-invariant norm"; their canonical witnesses quantified over
`KyFanDominantIdealFamily`, an implementation abstraction.  That is a genuine
theorem and a different quantifier.  *Repaired* by
`paperUINorm_of_kyFanDominant` -- Fan dominance, instantiating at the finite Ky
Fan gauges, which are themselves such families -- and six new paper-norm
endpoints derived through it.  The ideal-gauge forms are retained as supporting
evidence: they are stronger in their own quantifier.

**F3 — Theorem 6.3's witnesses were existential.**  The registered endpoints
returned `exists tanTheta0, ...` *inside* the ideal quantifier, so the
representative could differ from ideal to ideal and the statement could not be
promoted to one arbitrary norm.  *Repaired* by using the parameterized
paper-norm endpoints `tanTheta_directed_unboundedTrial_paperUINorm_complex` and
`..._real`, whose representative is a parameter characterized by its
approximation numbers.  (Those two were themselves replaced later the same day
as the `S2-tan-theta` directed witnesses -- see F9 -- but they remain Theorem
6.3's own witnesses, where the printed compression is bounded.)

**F4 — the `sin 2Theta` directed clauses cited no correspondence.**  Their
witnesses conclude on `sinTwoThetaIdealBlock`, the paper's reflected overlap
block, and the lemmas identifying its singular-value sequence with the directed
double-angle sine existed but were not registered on the clause.  *Repaired* by
citing `mem_sinTwoAngleOperatorC_iff`, `gauge_sinTwoAngleOperatorC`,
`sinTwoThetaIdealBlock_hasSameApproximationNumbers` and their real partners in
`evidence.correspondence`.

### Checker findings

**F5 — printed conclusions stated under `lemma` were unchecked.**  The
"every printed conclusion has an established clause" rule keyed on atoms of kind
`theorem` only.  Five counted results state their conclusion under `lemma`
(the four Section 6 lemmas) or `source-assertion` (Proposition 4.4, false as
printed), so for those the rule was vacuous: a clause could name no conclusion at
all.  *Repaired* by `CONCLUSION_ATOM_KINDS`, with a regression test.

**F6 — a clause's primary was not required to be canonical evidence.**  A
specialization or a presentation wrapper held as supporting evidence could be
named as a clause's primary witness; the coherence check would then have no
compiler-printed type and failed only incidentally.  *Repaired* and tested.

**F7 — a clause's scalar field was not checked against its primary.**  A row
could claim both of the paper's scalar fields while both clauses were witnessed
over the same one.  The canonical entry's `scalar_scope` is compiler-derived, so
requiring the clause to agree with it closes this.  *Repaired* and tested.

**F8 — the half-infinite gap justification was unchecked prose.**  That scope
cannot be decided from a printed type by a substring vocabulary -- three theorem
families spell it three ways -- so the clause records a justification instead.
Prose alone is an escape hatch.  *Repaired* by also requiring
`gap_scope_hypothesis_tokens`, each of which must occur in the primary's
compiler-printed type.

### Two things the review checked and did **not** change

*Theorem 8.1 part (iii) carries `FiniteDimensional`.*  That is the printed
scope: the source says "for every symmetric gauge function `Phi` in finite
dimensions".  Parts (i) and (ii) are proved without it, which is the source's own
"natural infinite-dimensional extensions".  No finite-dimensional theorem is
donating to an infinite-dimensional row.

*Proposition 4.4 is discharged by one counterexample.*  The source asserts the
printed proposition over a real or complex space, so a counterexample in either
field refutes it; requiring two would be requiring two counterexamples for one
false claim.  The checker now records that exemption explicitly rather than
leaving the row outside the scalar rule by accident.

## Second pass, same day: the unbounded-*compression* axis

The pass above separated "bounded ambient operator" from "unbounded ambient
operator" and found F1.  It did **not** separate a third scope from those two,
and the Palomar Section 2 Challenge audit -- written afterwards, against the
printed statements rather than against this certificate -- exposed it.

The three scopes are distinct:

| axis | source sentence | compiler-visible as |
|---|---|---|
| the ambient operator may be unbounded | S2: "also intended for unbounded self-adjoint `A`" | `→ₗ.[` in the printed type |
| the residual/perturbation must be bounded | S2: "no useful conclusion follows unless the residual is bounded" | `→L[` in the printed type |
| **the trial/Ritz compression may itself be unbounded** | Appendix to Section 6: "allows *both* `A₀` and `Λ₁` to be unbounded" | the carrier of the compression |

The source states the third one in as many words, and our own reconstruction
already spelled out the consequence: *"Thus the unbounded scope is stronger than
merely allowing the ambient self-adjoint operator to be unbounded while keeping
the Ritz compression bounded."*  The certificate could not check it, because
`DK-6-appendix.unbounded-tangent-extension` carried no `type_requirements` at
all -- the only scope atom on any Section 2 row that carried none.

### F9 — `S2-tan-theta`, directed clause, both fields

The registered primaries were
`tanTheta_directed_unboundedTrial_paperUINorm_{complex,real}`.  They take

```lean
TanTheta.UnboundedTrialBlock A Z   -- with   operator : Z →L[𝕜] Z
```

whose Ritz compression is **bounded and everywhere defined on the trial space**.
The bundle's name records only that the *ambient* operator is unbounded.  Both
theorems satisfy the first axis (`A : H →ₗ.[ℂ] H`) and the second (`residual :
Z →L[ℂ] H`), and neither establishes the third.  The 2026-08-12 acceptance note
is explicit that the Appendix obligation "is discharged by the new complex and
real unboundedCompression **ambient** endpoints" -- and then the row-level prose
said the directed conclusion was "closed at full source scope".  Nothing checked
the directed half against the atom it was credited with.

*Repaired* by `tanTheta_directed_unboundedRitz_paperUINorm_{complex,real}`,
which take `DavisKahan.UnboundedRitzPair A Z` -- whose
`trial.compression : Z →ₗ.[𝕜] Z` is a densely defined self-adjoint **partial
map** -- together with `ReducingComplement A V`, in the same vocabulary the
ambient clause already used.  This is a promotion, not new analysis: the
Appendix-scope Ky Fan estimates already existed on both fields
(`UnboundedCompressionTrialData.ideal_of_formBounds` over `ℂ`, proved through the
spectral cutoff `Ω(τ)` of the unbounded compression that the Appendix's own proof
uses at (6.9)--(6.10), and `theorem6_3_unboundedCompression_ideal_real` over
`ℝ` through the maintained complexification).  What was missing was the promotion
to the paper's universal norm quantifier.  The tangent representative stays a
parameter characterized by its approximation numbers, for the reason recorded on
the earlier endpoints: the promotion evaluates the estimate at every Ky Fan
index, and an existential could return a different representative at each one.

The bounded-compression declarations are retained as specializations.

### F10 — the certificate could not see the axis

*Repaired* by giving the atom

```json
"must_contain":     ["UnboundedRitzPair"],
"must_not_contain": ["UnboundedTrialBlock"]
```

so a bounded-compression bundle can no longer satisfy an Appendix-scope
obligation.  Measured against the actual compiler-printed types:

| declaration | ambient `→ₗ.` | residual `→L` | Appendix scope |
|---|---|---|---|
| `tanTheta_directed_unboundedRitz_paperUINorm_complex` | yes | yes | **PASS** |
| `tanTheta_directed_unboundedRitz_paperUINorm_real` | yes | yes | **PASS** |
| `tanTheta_directed_unboundedTrial_paperUINorm_complex` | yes | yes | **FAIL** |
| `tanTheta_directed_unboundedTrial_paperUINorm_real` | yes | yes | **FAIL** |
| `tanTheta_ambient_unboundedRitz_paperUINorm_complex` | yes | yes | **PASS** |
| `tanTheta_ambient_unboundedRitz_paperUINorm_real` | yes | yes | **PASS** |

The two `FAIL` rows are the point: they satisfy both older axes.  A single
generic `unbounded` token would have called them compliant, which is what
happened.  `scripts/tests/test_davis_kahan_coherent_evidence.py` carries the
negative regression (`unbounded ambient` + bounded compression must be rejected,
naming `UnboundedTrialBlock`) and the positive one.

### The narrow seven-clause audit on this axis

Every printed Section 2 clause, read off its canonical witness's
compiler-printed type.  "Block/compression unbounded" asks whether the operator
whose spectrum the gap hypothesis constrains is itself allowed to be a partial
map.

| clause | ambient unbounded | block/compression unbounded | how it is carried |
|---|---|---|---|
| `sin Θ` directed | yes | **yes** | `A₀ : F →ₗ.[𝕜] F` and `Λ₁ : G →ₗ.[𝕜] G` are both partial maps, and the residual `R : F →L[𝕜] E` is the only bounded object |
| `tan Θ` directed | yes | **yes**, after F9 | `UnboundedRitzPair.trial.compression : Z →ₗ.[𝕜] Z` |
| `tan Θ` ambient | yes | **yes** | same carrier |
| `sin 2Θ` directed | yes | **no** — see below | `M : ↥V →L[ℂ] ↥V` |
| `sin 2Θ` ambient | yes | n/a | no trial compression appears; the perturbation `Eop : Hc →L[ℂ] Hc` is bounded, as the source requires |
| `tan 2Θ` directed | yes | **yes** | there is no separate compression object: the blocks are `A` itself restricted to `specRange hA (Set.Iic c)` and its complement, and the hypotheses are form bounds `re ⟪A x, x⟫ ≤ a‖x‖²` quantified over `x : A.domain` |
| `tan 2Θ` ambient | yes | **yes** | same |

Two remarks on that table.

*`sin Θ` is stronger than the Appendix sentence.*  The Appendix says "one of
`A₀`, `Λ₁` may be unbounded"; the witness allows both, independently.  The
carrier `IsExactSpectralDecomposition` is, despite its name, **not** a
spectrality assumption -- its fields are two complementary isometries and an
intertwining, i.e. an arbitrary reducing decomposition.

*`tan 2Θ` has no hidden bounded compression.*  The suspicion was worth checking
and does not apply: nothing plays the role `UnboundedTrialBlock.operator` played
for `tan Θ`.  Its exact subspace is spectral (`specRange hA (Set.Iic c)`), but
for the **ordered** families that is forced rather than assumed: `spec(A₀) ⊆
[β,α]` and `spec(A₁) ⊆ [α+δ,∞)` leave `A` no spectrum in `(α, α+δ)`, so `P` is
the spectral projector for `(-∞,α]`.  The same argument covers the ordered
`tan Θ` families.

### `sin 2Θ` directed: why the compression stays bounded

The Appendix enumerates which results get which relaxation, and the enumeration
is exhaustive where it is stated:

> For the sine theorem, one of `A₀,Λ₁` may be unbounded. […] **Proposition 6.1
> and Theorem 6.1 admit the analogous relaxation.**
>
> For the tangent theorem the Appendix explicitly returns to the ordered
> hypotheses […] and allows *both* `A₀` and `Λ₁` to be unbounded […] The same
> method is stated to extend **Theorem 6.3** to unbounded operators.

Proposition 6.1 and Theorem 6.1 are the generalized **sine** results; Theorem 6.3
is the **tangent** one.  Neither the `sin 2Θ` nor the `tan 2Θ` theorem is named
anywhere in the Appendix, and no other source passage extends a double-angle
result to an unbounded compression.  What does apply to all four is the general
`S2-unbounded-scope` paragraph -- unbounded self-adjoint `A`, bounded
perturbation or residual -- and the `sin 2Θ` witnesses satisfy it.

So no counted obligation is open here, and no atom is added.  What is recorded,
so that it is challengeable rather than invisible:

1. `hVdom : ∀ v : ↥V, ↑v ∈ A.domain` puts the **whole** trial subspace inside the
   domain.  Given that, `M` being bounded is not a further restriction: `A` is
   closed and `V` is complete, so `A|_V` is bounded by the closed graph theorem.
   The single restriction is `hVdom` itself, against the source's own preferred
   spelling for the unbounded sine passage, where `(A+H)E₀` and `E₀A₀` "share a
   dense domain" and `R` is extended by continuity.  The source uses that
   spelling for the sine theorem and does not use it for `sin 2Θ`.
2. `sin 2Θ`'s exact subspace is built spectrally
   (`selfAdjointSpectralSubspace A hA B hB`), whereas Section 1 says "No
   assumption is made here that `P` or `Q` is a spectral projector".  That
   sentence is atom `S1-block-residual.no-spectral-projector-assumption`, which
   the accepted boundary review classifies `source_wide_setup` / `non_result`
   and links to no counted result -- the standing generality of the block
   framework rather than a proved-scope extension of any theorem.  A reviewer may
   disagree with that classification; it is recorded, not silent.  A strictly
   more general **ambient** `sin 2Θ` theorem does already exist in the tree,
   `sinTwoTheta_ambient_reflection_projectorDifference_paperUINorm`, at arbitrary
   reducing `U` and `V`; it is not the registered canonical witness because the
   registered one concludes on the paper's `sin 2Θ` angle operator directly.

### Effect on the count

29/29, unchanged.  One clause's canonical evidence was replaced, no result was
added, removed, or reclassified, and no boundary review changed.  The count was
provisionally suspect for the duration of this pass and is restored on the
repair, not on the argument.

## Disposition of every counted result

Every row below is **PASS**: each printed clause has one coherent
compiler-checked witness at the same scalar, operator, dimensional, norm, gap and
angle scope, with no clause open.

### `S2-sin-theta` — Single-angle sine theorem

- Source: Section 2, sin theta theorem
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `directed.complex` | complex | `S2-sin-theta.directed-conclusion` | `DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_complex` | **PASS** |
  | `directed.real` | real | `S2-sin-theta.directed-conclusion` | `DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_real` | **PASS** |

- Result-wide scope atoms carried by every clause's own primary: `S2-sin-theta.ui-norm-scope`, `S2-sin-theta.gap-hypothesis`, `S2-unbounded-scope.infinite-dimensional-scope`, `S2-unbounded-scope.arbitrary-ui-scope`, `S2-unbounded-scope.unbounded-selfadjoint-scope`, `S2-unbounded-scope.bounded-residual-needed`, `S2-unbounded-scope.half-infinite-gap-intervals`

### `S2-tan-theta` — Single-angle tangent theorem

- Source: Section 2, tan theta theorem
- Alignment: `paper_faithful_nonlocal_source_interpretation`; locally self-contained: False
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `ambient.complex` | complex | `S2-tan-theta.ambient-conclusion` | `TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_paperUINorm_complex` | **PASS** |
  | `ambient.real` | real | `S2-tan-theta.ambient-conclusion` | `TauCeti.DavisKahan1970.tanTheta_ambient_unboundedRitz_paperUINorm_real` | **PASS** |
  | `directed.complex` | complex | `S2-tan-theta.directed-conclusion` | `TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_paperUINorm_complex` | **PASS** (F9) |
  | `directed.real` | real | `S2-tan-theta.directed-conclusion` | `TauCeti.DavisKahan1970.tanTheta_directed_unboundedRitz_paperUINorm_real` | **PASS** (F9) |

- Result-wide scope atoms carried by every clause's own primary: `S2-sin-theta.ui-norm-scope`, `S2-tan-theta.ordered-gap-hypothesis`, `S2-tan-theta.rayleigh-ritz-hypothesis`, `S2-unbounded-scope.infinite-dimensional-scope`, `S2-unbounded-scope.arbitrary-ui-scope`, `S2-unbounded-scope.unbounded-selfadjoint-scope`, `S2-unbounded-scope.bounded-residual-needed`, `S2-unbounded-scope.half-infinite-gap-intervals`, `DK-6-appendix.unbounded-tangent-extension`

### `S2-sin-two-theta` — Double-angle sine theorem

- Source: Section 2, sin 2 theta theorem
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `directed.residual.complex` | complex | `S2-sin-two-theta.directed-conclusion` | `TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_complex` | **PASS** |
  | `directed.residual.real` | real | `S2-sin-two-theta.directed-conclusion` | `TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_real` | **PASS** |
  | `ambient.complex` | complex | `S2-sin-two-theta.ambient-conclusion` | `TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_addBounded_paperUINorm_complex` | **PASS** |
  | `ambient.real` | real | `S2-sin-two-theta.ambient-conclusion` | `TauCeti.DavisKahan1970.sinTwoTheta_ambient_unbounded_addBounded_paperUINorm_real` | **PASS** |

- Correspondence lemmas registered: `TauCeti.DavisKahan.mem_sinTwoAngleOperatorC_iff`, `TauCeti.DavisKahan.gauge_sinTwoAngleOperatorC`, `TauCeti.DavisKahan.sinTwoThetaIdealBlock_hasSameApproximationNumbers`, `TauCeti.DavisKahan.mem_sinTwoAngleOperatorRC_iff`, `TauCeti.DavisKahan.gauge_sinTwoAngleOperatorRC`
- Result-wide scope atoms carried by every clause's own primary: `S2-sin-theta.ui-norm-scope`, `S2-sin-two-theta.gap-hypothesis`, `S2-unbounded-scope.infinite-dimensional-scope`, `S2-unbounded-scope.arbitrary-ui-scope`, `S2-unbounded-scope.unbounded-selfadjoint-scope`, `S2-unbounded-scope.bounded-residual-needed`, `S2-unbounded-scope.half-infinite-gap-intervals`

### `S2-tan-two-theta` — Double-angle tangent theorem

- Source: Section 2, tan 2 theta theorem
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `directed.complex` | complex | `S2-tan-two-theta.directed-conclusion` | `TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_complex` | **PASS** |
  | `directed.real` | real | `S2-tan-two-theta.directed-conclusion` | `TauCeti.DavisKahan1970.tanTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_real` | **PASS** |
  | `ambient.complex` | complex | `S2-tan-two-theta.ambient-conclusion` | `TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_paperUINorm_complex` | **PASS** |
  | `ambient.real` | real | `S2-tan-two-theta.ambient-conclusion` | `TauCeti.DavisKahan1970.tanTwoTheta_ambient_unbounded_paperUINorm_real` | **PASS** |

- Result-wide scope atoms carried by every clause's own primary: `S2-sin-theta.ui-norm-scope`, `S2-tan-two-theta.ordered-gap-hypothesis`, `S2-tan-two-theta.strong-offdiagonal-hypothesis`, `S2-tan-two-theta.no-extra-pole-hypothesis`, `S2-unbounded-scope.infinite-dimensional-scope`, `S2-unbounded-scope.arbitrary-ui-scope`, `S2-unbounded-scope.unbounded-selfadjoint-scope`, `S2-unbounded-scope.bounded-residual-needed`, `S2-unbounded-scope.half-infinite-gap-intervals`

### `DK-3.1-prop` — Acute direct rotation existence and uniqueness

- Source: Proposition 3.1
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `existence.rclike` | rclike | `DK-3.1-prop.existence`, `DK-3.1-prop.uniqueness`, `DK-3.1-prop.positive-diagonal-characterization` | `TauCeti.DavisKahan1970.proposition3_1_source` | **PASS** |


### `DK-3.2-prop` — Nonacute existence criterion

- Source: Proposition 3.2
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `existence-iff-crossing-dimensions.rclike` | rclike | `DK-3.2-prop.existence-iff-crossing-dimensions` | `TauCeti.DavisKahan1970.proposition3_2_exists_iff_crossedDefectsEquivalent` | **PASS** |
  | `nonuniqueness.rclike` | rclike | `DK-3.2-prop.nonuniqueness` | `TauCeti.DavisKahan1970.proposition3_2_not_unique` | **PASS** |

- Result-wide scope atoms carried by every clause's own primary: `DK-3.2-prop.eq-3-5`

### `DK-3.3-prop` — Principal square-root characterization

- Source: Proposition 3.3
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `principal-square-root.complex` | complex | `DK-3.3-prop.principal-square-root` | `TauCeti.DavisKahan1970.proposition3_3_complex_forward_source` | **PASS** |
  | `square-root-converse.complex` | complex | `DK-3.3-prop.square-root-converse` | `TauCeti.DavisKahan1970.proposition3_3_complex_converse_source` | **PASS** |
  | `principal-square-root.real` | real | `DK-3.3-prop.principal-square-root` | `TauCeti.DavisKahan1970.proposition3_3_real_forward_source` | **PASS** |
  | `square-root-converse.real` | real | `DK-3.3-prop.square-root-converse` | `TauCeti.DavisKahan1970.proposition3_3_real_converse_source` | **PASS** |


### `DK-3.4-prop` — Square as a direct rotation

- Source: Proposition 3.4
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `u-square-direct-rotation.complex` | complex | `DK-3.4-prop.u-square-direct-rotation` | `TauCeti.DavisKahan1970.proposition3_4_source_full_complex` | **PASS** |
  | `u-square-direct-rotation.real` | real | `DK-3.4-prop.u-square-direct-rotation` | `TauCeti.DavisKahan1970.proposition3_4_source_full_real` | **PASS** |

- Result-wide scope atoms carried by every clause's own primary: `S3-standing-scope.crossed-dimension-standing-assumption`

### `DK-3.1-thm` — Classification of pairs of subspaces

- Source: Theorem 3.1
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `complete-invariant.complex` | complex | `DK-3.1-thm.complete-invariant` | `TauCeti.DavisKahan1970.theorem3_1_spectralMultiplicity_classification_complex` | **PASS** |
  | `complete-invariant.real` | real | `DK-3.1-thm.complete-invariant` | `TauCeti.DavisKahan1970.theorem3_1_spectralMultiplicity_classification_real` | **PASS** |
  | `converse-angle-data.rclike` | rclike | `DK-3.1-thm.converse-angle-data` | `TauCeti.DavisKahan1970.theorem3_1_realization` | **PASS** |


### `DK-3.1-cor` — Compact classification by angle eigenvalues

- Source: Corollary 3.1
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `compact-complete-invariants.rclike` | rclike | `DK-3.1-cor.compact-complete-invariants`, `DK-3.1-cor.theta1-match` | `TauCeti.DavisKahan1970.corollary3_1_compact_defectBlock_angleList_classification` | **PASS** |
  | `allowed-angle-sequence.rclike` | rclike | `DK-3.1-cor.allowed-angle-sequence` | `TauCeti.DavisKahan1970.corollary3_1_realization` | **PASS** |


### `DK-3.5-prop` — Angle commutation and eigenspace geometry

- Source: Proposition 3.5
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `commutation.rclike` | rclike | `DK-3.5-prop.commutation` | `TauCeti.DavisKahan1970.proposition3_5_commutations` | **PASS** |
  | `eigenvector-rotation-angle.rclike` | rclike | `DK-3.5-prop.eigenvector-rotation-angle` | `TauCeti.DavisKahan1970.proposition3_5_eigenvector_angle` | **PASS** |
  | `acute-maximal-characterization.rclike` | rclike | `DK-3.5-prop.acute-maximal-characterization` | `TauCeti.DavisKahan1970.proposition3_5_angleEigenspace_uniqueMaximal` | **PASS** |


### `DK-3.2-cor` — Reversal symmetry

- Source: Corollary 3.2
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `swap-invariance.rclike` | rclike | `DK-3.2-cor.swap-invariance` | `TauCeti.DavisKahan1970.corollary3_2_source` | **PASS** |


### `DK-4.1-prop` — Pointwise and singular-value extremality of the direct rotation

- Source: Proposition 4.1
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `orthonormal-angle-lower-bounds.complex` | complex | `DK-4.1-prop.orthonormal-angle-lower-bounds`, `DK-4.1-prop.singular-value-minimality` | `TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute_complex` | **PASS** |
  | `orthonormal-angle-lower-bounds.real` | real | `DK-4.1-prop.orthonormal-angle-lower-bounds`, `DK-4.1-prop.singular-value-minimality` | `TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute_real` | **PASS** |


### `DK-4.1-cor` — UI-norm minimality of direct rotation displacement

- Source: Corollary 4.1
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `ui-minimality-on-p.complex` | complex | `DK-4.1-cor.ui-minimality-on-p` | `TauCeti.DavisKahan1970.Corollary4_1_compact_nonacute_paperUINorm_complex` | **PASS** |
  | `ui-minimality-on-p.real` | real | `DK-4.1-cor.ui-minimality-on-p` | `TauCeti.DavisKahan1970.Corollary4_1_compact_nonacute_paperUINorm_real` | **PASS** |


### `DK-4.2-prop` — Basis-angle square-sum extremality

- Source: Proposition 4.2
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `basis-sine-square-lower-bound.complex` | complex | `DK-4.2-prop.basis-sine-square-lower-bound` | `TauCeti.DavisKahan1970.Proposition4_2_infiniteDimensional` | **PASS** |
  | `basis-sine-square-lower-bound.real` | real | `DK-4.2-prop.basis-sine-square-lower-bound` | `TauCeti.DavisKahan1970.tsum_displacementAngleSineSqR_ge_tsum_sq_sin_principalAngleSequence` | **PASS** |


### `DK-4.3-prop` — Squared displacement UI-norm minimality

- Source: Proposition 4.3
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `squared-displacement-global-minimum.complex` | complex | `DK-4.3-prop.squared-displacement-global-minimum` | `TauCeti.DavisKahan1970.Proposition4_3_compact_nonacute_paperUINorm_complex` | **PASS** |
  | `squared-displacement-global-minimum.real` | real | `DK-4.3-prop.squared-displacement-global-minimum` | `TauCeti.DavisKahan1970.Proposition4_3_compact_nonacute_paperUINorm_real` | **PASS** |


### `DK-4.4-prop` — Full-displacement counterexamples and Proposition 4.4 as printed

- Source: Proposition 4.4
- Alignment: `refuted_as_transcribed`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `whole.not_visible_in_type` | not_visible_in_type | `DK-4.4-prop.printed-proposition4-4` | `TauCeti.DavisKahanTheory.not_davisKahanProposition4_4_Finite` | **PASS** |

- Result-wide scope atoms carried by every clause's own primary: `DK-4.4-prop.printed-proposition4-4`

### `DK-5.1-thm` — Banach-space Sylvester lower bound

- Source: Theorem 5.1
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `sylvester-lower-bound.scalar_generic` | scalar_generic | `DK-5.1-thm.sylvester-lower-bound` | `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_uiNorm` | **PASS** |
  | `sylvester-lower-bound.complex` | complex | `DK-5.1-thm.sylvester-lower-bound` | `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_exact` | **PASS** |

- Result-wide scope atoms carried by every clause's own primary: `DK-5.1-thm.banach-hypotheses`

### `DK-5.2-thm` — Semibounded self-adjoint Sylvester theorem

- Source: Theorem 5.2
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `hilbert-unbounded-conclusion.complex` | complex | `DK-5.2-thm.hilbert-unbounded-conclusion` | `TauCeti.DavisKahan1970.theorem5_2_paperUINorm_complex` | **PASS** |
  | `hilbert-unbounded-conclusion.real` | real | `DK-5.2-thm.hilbert-unbounded-conclusion` | `TauCeti.DavisKahan1970.theorem5_2_paperUINorm_real` | **PASS** |

- Result-wide scope atoms carried by every clause's own primary: `DK-5.2-thm.hilbert-unbounded-hypotheses`

### `DK-5.1-lem` — Strong-cutoff convergence of singular values

- Source: Lemma 5.1
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `whole.rclike` | rclike | `DK-5.1-lem.strong-cutoff-convergence` | `TauCeti.DavisKahan1970.Lemma5_1` | **PASS** |

- Result-wide scope atoms carried by every clause's own primary: `DK-5.1-lem.strong-cutoff-convergence`

### `DK-6.1-lem` — Direct-sum UI-norm comparison and converse

- Source: Lemma 6.1
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `whole.rclike` | rclike | `DK-6.1-lem.ordered-sylvester-forward` | `TauCeti.DavisKahan1970.lemma6_1` | **PASS** |
  | `whole.rclike.2` | rclike | `DK-6.1-lem.ordered-sylvester-converse` | `TauCeti.DavisKahan1970.lemma6_1_converse` | **PASS** |

- Result-wide scope atoms carried by every clause's own primary: `DK-6.1-lem.ordered-sylvester-forward`, `DK-6.1-lem.ordered-sylvester-converse`

### `DK-6.2-lem` — Reflection-pinch contraction

- Source: Lemma 6.2
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `whole.rclike` | rclike | `DK-6.2-lem.pinching-contraction` | `TauCeti.DavisKahan1970.lemma6_2` | **PASS** |

- Result-wide scope atoms carried by every clause's own primary: `DK-6.2-lem.pinching-contraction`

### `DK-6.1-prop` — Sine proof, ambient limitation, and symmetric sine theorem

- Source: Proposition 6.1
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `symmetric-sine-theorem.complex` | complex | `DK-6.1-prop.symmetric-sine-theorem` | `TauCeti.DavisKahan1970.proposition6_1_source_complex` | **PASS** |
  | `symmetric-sine-theorem.real` | real | `DK-6.1-prop.symmetric-sine-theorem` | `TauCeti.DavisKahan1970.proposition6_1_source_real` | **PASS** |


### `DK-6.1-thm` — Generalized sine theorem

- Source: Theorem 6.1
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `generalized-sine-conclusion.complex` | complex | `DK-6.1-thm.generalized-sine-conclusion` | `TauCeti.DavisKahan1970.theorem6_1_source_complex` | **PASS** |
  | `generalized-sine-conclusion.real` | real | `DK-6.1-thm.generalized-sine-conclusion` | `TauCeti.DavisKahan1970.theorem6_1_source_real` | **PASS** |

- Result-wide scope atoms carried by every clause's own primary: `DK-6.1-thm.generalized-sine-hypotheses`, `DK-6.1-thm.unequal-dimension-scope`

### `DK-6.2-thm` — Pairwise-gap square-norm sine theorem

- Source: Theorem 6.2
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `second-generalized-sine.complex` | complex | `DK-6.2-thm.second-generalized-sine` | `TauCeti.DavisKahan1970.theorem6_2_source_complex` | **PASS** |
  | `second-generalized-sine.real` | real | `DK-6.2-thm.second-generalized-sine` | `TauCeti.DavisKahan1970.theorem6_2_source_real` | **PASS** |


### `DK-6.3-thm` — Tangent proof machinery, Example 6.1, and generalized tangent theorem

- Source: Theorem 6.3
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `generalized-tangent-theorem.complex` | complex | `DK-6.3-thm.generalized-tangent-theorem` | `TauCeti.DavisKahan1970.tanTheta_directed_unboundedTrial_paperUINorm_complex` | **PASS** |
  | `generalized-tangent-theorem.real` | real | `DK-6.3-thm.generalized-tangent-theorem` | `TauCeti.DavisKahan1970.tanTheta_directed_unboundedTrial_paperUINorm_real` | **PASS** |


### `DK-6.3-lem` — Finite-rank near-maximizer leakage estimate

- Source: Lemma 6.3
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `whole.complex` | complex | `DK-6.3-lem.approximation-number-leakage` | `TauCeti.DavisKahan1970.Section6Appendix.lemma6_3_approximationNumber_leakage_complex` | **PASS** |
  | `whole.real` | real | `DK-6.3-lem.approximation-number-leakage` | `TauCeti.DavisKahan1970.Section6Appendix.lemma6_3_approximationNumber_leakage_real` | **PASS** |

- Result-wide scope atoms carried by every clause's own primary: `DK-6.3-lem.approximation-number-leakage`

### `DK-8.1-thm` — Branch selection and spectral repulsion

- Source: Theorem 8.1
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `existence-correct-q.complex` | complex | `DK-8.1-thm.existence-correct-q` | `TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranch` | **PASS** |
  | `existence-correct-q.real` | real | `DK-8.1-thm.existence-correct-q` | `TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranch_real` | **PASS** |
  | `acute-iff-spectral-placement.complex` | complex | `DK-8.1-thm.acute-iff-spectral-placement` | `TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_spectrumIn` | **PASS** |
  | `acute-iff-spectral-placement.real` | real | `DK-8.1-thm.acute-iff-spectral-placement` | `TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_spectrumIn_real` | **PASS** |
  | `part-i-compression.complex` | complex | `DK-8.1-thm.part-i-compression` | `TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_source` | **PASS** |
  | `part-i-compression.complex.2` | complex | `DK-8.1-thm.part-i-compression` | `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_source` | **PASS** |
  | `part-i-compression.real` | real | `DK-8.1-thm.part-i-compression` | `TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_real` | **PASS** |
  | `part-i-compression.real.2` | real | `DK-8.1-thm.part-i-compression` | `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_real` | **PASS** |
  | `part-ii-eigenvalue.complex` | complex | `DK-8.1-thm.part-ii-eigenvalue` | `TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_source` | **PASS** |
  | `part-ii-eigenvalue.complex.2` | complex | `DK-8.1-thm.part-ii-eigenvalue` | `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_source` | **PASS** |
  | `part-ii-eigenvalue.real` | real | `DK-8.1-thm.part-ii-eigenvalue` | `TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_real` | **PASS** |
  | `part-ii-eigenvalue.real.2` | real | `DK-8.1-thm.part-ii-eigenvalue` | `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_real` | **PASS** |
  | `part-iii-gauge.complex` | complex | `DK-8.1-thm.part-iii-gauge` | `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_angle_rev_source` | **PASS** |
  | `part-iii-gauge.complex.2` | complex | `DK-8.1-thm.part-iii-gauge` | `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev_source` | **PASS** |
  | `part-iii-gauge.real` | real | `DK-8.1-thm.part-iii-gauge` | `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_angle_rev_real` | **PASS** |
  | `part-iii-gauge.real.2` | real | `DK-8.1-thm.part-iii-gauge` | `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev_real` | **PASS** |


### `DK-8.2-thm` — Smallness selects the acute branch

- Source: Theorem 8.2
- Alignment: `locally_exact`; locally self-contained: True
- Printed clauses (one row per clause per scalar field):

  | clause | field | conclusion atom(s) | canonical witness | disposition |
  |---|---|---|---|---|
  | `acute-branch-conclusion.complex` | complex | `DK-8.2-thm.acute-branch-conclusion` | `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_maximalAngle_lt_of_crossedDefects` | **PASS** |
  | `acute-branch-conclusion.real` | real | `DK-8.2-thm.acute-branch-conclusion` | `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_real_maximalAngle_lt_of_crossedDefects` | **PASS** |
  | `double-angle-bound-retained.complex` | complex | `DK-8.2-thm.double-angle-bound-retained` | `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source_paperUINorm` | **PASS** |
  | `double-angle-bound-retained.complex.2` | complex | `DK-8.2-thm.double-angle-bound-retained` | `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_source_paperUINorm` | **PASS** |
  | `double-angle-bound-retained.real` | real | `DK-8.2-thm.double-angle-bound-retained` | `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source_real_paperUINorm` | **PASS** |
  | `double-angle-bound-retained.real.2` | real | `DK-8.2-thm.double-angle-bound-retained` | `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_source_real_paperUINorm` | **PASS** |

- Result-wide scope atoms carried by every clause's own primary: `DK-8.2-thm.smallness-alternative`, `S3-standing-scope.crossed-dimension-standing-assumption`

