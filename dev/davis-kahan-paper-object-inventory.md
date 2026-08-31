# The `Paper*` objects the 29 counted results actually depend on

**Purpose.** `Paper`-prefixed names are used in this tree for three genuinely
different jobs, and the prefix does not say which. This file separates them, for
the objects that appear in the *compiler-printed types* of the canonical evidence
for the 29 counted Davis--Kahan 1970 results. It is a design classification, not
a status ledger; it does not restate what is proved.

**Do not read the `paper` prefix as "removable".** Two entries below are
different operators from their unprefixed namesakes, and one of those distinctions
(directed versus ambient angle multiplicity) has already cost this development a
false claim.

## How the inventory was extracted

```bash
lake build DavisKahan.Sources.DavisKahan1970.Audits.ResultSemanticSurface
lake env lean DavisKahan/Sources/DavisKahan1970/Audits/ResultSemanticSurface.lean
```

That surface `#check`s every declaration registered by
`dev/davis-kahan-1970-formalization-result-inventory.json`. Splitting its output
into `@Name : type` blocks, restricting to the declarations each result names as
`canonical_evidence`, and collecting identifiers matching `[Pp]aper[A-Za-z0-9_]*`
from those types gives the table below. Name *fragments* (`paperUINorm_complex`
and friends, which are parts of theorem names rather than objects) are excluded.

Both unmatched canonical declarations at extraction time --
`corollary3_1_realization` and `not_davisKahanProposition4_4_Finite` -- print
types with no `Paper*` object in them.

## Classification

- **A — canonical mathematical object.** Reusable mathematics that should keep a
  stable API and could be stated for anyone; the `paper` prefix is historical.
- **B — source-correspondence object.** Exists to name what Davis and Kahan
  literally write. It belongs in the Davis--Kahan source layer and should stay
  there even when an equivalent cleaner object exists, because the equivalence is
  itself a source-fidelity claim.
- **C — compatibility/proof adapter.** The consuming theorem should eventually be
  restated on a cleaner abstraction; the object exists because of how the current
  proof is organised.
- **D — proof vehicle.** Should never appear in a canonical theorem signature.

**No row is class D.** That is deliberate and is a checkable invariant, not an
accident: the two objects first classified D both appeared in canonical theorem
types, which means the classification was wrong rather than the theorems. If a
future row is D, the canonical theorem naming it is the thing to fix.

| object | class | results whose canonical evidence names it | why |
| --- | --- | --- | --- |
| `PaperUnitaryInvariantNorm` | **C** | S2 ×4, DK-6.1-lem, DK-6.1-prop, DK-6.1-thm, DK-6.2-lem, DK-8.2-thm | See "The norm layer" below. It is the operational adapter from Ky Fan estimates to the source's universal norm quantifier, and it is the single most load-bearing `Paper*` object in the tree. |
| `PaperSymmetricNormingFunction` | **B** | (not in a canonical type; reached through the equivalence) | The finite-list symmetric norming function Davis and Kahan actually define. `TauCeti.DavisKahan.ExactSinTheta.paperNormEquiv` is a full `Equiv` to `PaperUnitaryInvariantNorm`, with `ofPaperNorm_toPaperNorm` and `toPaperNorm_ofPaperNorm_finite_apply` as the two round trips. |
| `paperSinAngleOperatorC` | **B** | DK-6.1-prop | The paper's *ambient* sine-angle operator. `paperSinAngleOperatorC_eq` characterizes it. Distinct from the directed `sinAngleOperatorC`. |
| `paperTanAngleOperatorC` / `…R` | **B** | S2-tan-theta | The paper's ambient tangent. `paperTanAngleOperatorC_eq_cfc` gives the functional-calculus form under transversality; `paperTanAngleOperatorC_eq_modulus_blockRepresentative` gives the block form. `…R` is defined by transport through complexification. |
| `paperSinTwoAngleOperatorC` / `…R` | **B** | S2-sin-two-theta, DK-8.2-thm | The paper's ambient `sin 2Θ`. `norm_paperSinTwoAngleOperatorC_eq_norm_sinTwoAngleOperatorC` relates it to the directed operator **in operator norm only**; the approximation-number identification is claimed for the directed operator, not this one. That is a real distinction: an ambient angle object carries each principal angle twice where the directed block carries it once. |
| `paperAbsTanTwoAngleOperatorC` / `…R` | **B** | S2-tan-two-theta | The paper's branch-free ambient `|tan 2Θ|`. `paperAbsTanTwoAngleOperatorC_eq_paperTanTwoAngleOperatorC` and `…_eq_modulus_paperTanTwoAngleOperatorC` are the characterizations; the branch-free form is the one definable with no quarter-acute hypothesis. |
| `PaperTheorem61Data`, `PaperRealTheorem61Data` | **C — replacement landed** | (no longer canonical) | Source-shaped data bundles for Theorem 6.1, each wrapping a further `UnboundedSinThetaData` record. Replaced as canonical evidence on 2026-08-31 by `theorem6_1_source_complex` / `..._real`, which take components. Retained as the implementation and compatibility API. |
| `PaperTheorem62Data`, `PaperRealTheorem62Data` | **C — replacement landed** | (no longer canonical) | As above; replaced by `theorem6_2_source_complex` / `..._real`. |
| `PaperSymmetricSinThetaProblem`, `PaperRealSymmetricSinThetaProblem` | **C — replacement landed** | (no longer canonical) | As above; replaced by `proposition6_1_source_complex` / `..._real`. The Challenge wrapper `sinTheta_wholeSpace_paperUINorm`, which had demonstrated the direct-hypothesis API, is now an alias of the production declaration. |
| `PaperSinThetaRepresentativeAcross` | **A** | DK-6.1-thm, DK-6.2-thm | Not source vocabulary: it is the statement that two operators across different spaces have the same singular-value data, which is what lets a unitarily invariant norm be evaluated on either. Reusable as it stands. |
| `paperHilbertSchmidtNorm`, `IsPaperHilbertSchmidt` | **B** | DK-6.2-thm | Theorem 6.2 is printed *for the Hilbert--Schmidt norm specifically*, with the source's lower-frame factor. The named object is what makes that printed specialization visible rather than hidden inside a general gauge. |
| `paperProjectionBlock` | **A** | DK-6.1-lem | A projection block between two subspaces. `paperProjectionBlock_eq_subtypeL_comp` identifies it with the ordinary composite; nothing about it is Davis--Kahan specific. |
| `paperBlockCompression` | **A** | S2-tan-two-theta | Compression of an operator to a block. `paperBlockCompression_complexify_equiv` transports it through complexification. Ordinary mathematics. |
| `paperDiagonalPair` | **B** *(was D)* | DK-6.2-lem | `2·(pair) = R_U + R_Uᗮ` (`two_smul_paperDiagonalPair_eq_add_reflections`), i.e. the pinching `T ↦ P_U T P_U + P_Uᗮ T P_Uᗮ`. Lemma 6.2 **is** the statement that this contracts every Ky Fan gauge, so the object is what the printed lemma is about, not a vehicle for proving something else. Class D said "never appears in a canonical theorem signature", and this one does; the D label was the error, not the signature. |
| `paperCrossSineSum` | **C** *(was D)* | (no longer canonical) | `P_Uᗮ P_V + P_U P_Vᗮ`. Not a proof-only object either: it appeared in the conclusion of the real Proposition 6.1 theorem. It is a **representation adapter** — `paperCrossSineSum_same_projectionDiff` gives it exactly the approximation-singular sequence of `P_V − P_U`, and it is used because there is no real continuous functional calculus here, so no literal real `sin Θ` operator exists to conclude on. As of 2026-08-31 the canonical real Proposition 6.1 concludes on the projector difference instead, through that transport, and this object no longer appears in any canonical signature. |
| `corollary3_2_paperQuarterTurn` | **B** | DK-3.2-cor, DK-3.5-prop | The paper's quarter-turn used in Corollary 3.2's symmetry statement; source vocabulary for a specific printed construction. |
| `IsPaperDirectRotation` | **B** | DK-3.2-prop | Definition 3.1's direct rotation, as printed. Kept deliberately distinct from stronger operator-positivity spellings: `proposition3_4_source_full_bundled_complex` was once accepted against this predicate and had to be repaired, because over `ℂ` its diagonal clauses do not force self-adjointness of the compression while Definition 3.1 asks for genuine positivity. `crossedDefectEquivOfPaperDirectRotation` is the bridge to the crossed-defect data. |

## The norm layer

The three objects in play are:

* `TauCeti.DavisKahan.ExactSinTheta.PaperUnitaryInvariantNorm` — a *sequence* of
  finite unitarily invariant seminorms `TauCeti.UnitarilyInvariantSeminorm ℂ
  (EuclideanSpace ℂ (Fin n))`, plus `normalized` and `zero_pad`, extended to
  operators by `extendedGauge A = ⨆ n, ofReal (prefixGauge n A)` over the
  approximation-number prefixes, with `Mem A ↔ extendedGauge A ≠ ⊤`.
* `TauCeti.DavisKahan.ExactSinTheta.PaperSymmetricNormingFunction` — the
  finite-list object, `gauge : ∀ n, (Fin n → ℝ) → ℝ` with the printed axioms.
* `TauCeti.SymmetricGauge` (`ForTauCeti/Analysis/Normed/SymmetricGauge.lean`) —
  Calkin's symmetric norming function on `(ℕ →₀ ℝ≥0)`, with `extend` to
  `ℕ → ℝ≥0∞`.

The first two are already tied: `paperNormEquiv : PaperUnitaryInvariantNorm ≃
PaperSymmetricNormingFunction`, both round trips proved. So the *source*
correspondence is closed, and the open architectural question is only whether
`TauCeti.SymmetricGauge` can replace `PaperUnitaryInvariantNorm` as the durable
abstraction underneath.

**It cannot today, and the blocker is at the operator-ideal layer, not at the
gauge layer.** `TauCeti.symmetricGaugeFamily`, the construction that turns a
`SymmetricGauge` into an operator ideal family, is

```lean
noncomputable def symmetricGaugeFamily : OperatorIdealFamily ℂ
```

in `ForTauCeti/Analysis/OperatorIdeal/Family/SymmetricGauge.lean`, and every
theorem it is built from (`approxSeq`, `extend_approxSeq_add_le`,
`extend_approxSeq_smul`, `enorm_le_extend_approxSeq`, `extend_approxSeq_comp_le`)
is stated with `[InnerProductSpace ℂ E]`. The file states the reason itself:
`ContinuousLinearMap.kyFanGauge_add_le_complex` is unconditional over `ℂ`, while
its `RCLike`-generic counterpart carries
`ContinuousLinearMap.HasMinMaxLowerBoundEverywhere 𝕜`, so a general-field family
would have to carry that class in its signature — and the accepted roadmap states
the family over `ℂ`.

`PaperUnitaryInvariantNorm` has no such restriction: its `gauge` is real-valued
and its `Mem`/`extendedGauge` are stated for `A : E →L[𝕜] F` with `[RCLike 𝕜]`
and unequal source and target spaces, which is exactly why the real and
rectangular Davis--Kahan endpoints can use it. Migrating the 29-result surface
onto `SymmetricGauge` today would therefore lose real scalar support and
rectangular operator support at the ideal layer.

**Consequently the norm pilot in the current pass is not attempted.** The precise
missing object is an `RCLike`-generic `symmetricGaugeFamily`, i.e. an
`OperatorIdealFamily 𝕜` for `[RCLike 𝕜]`, presumably carrying
`HasMinMaxLowerBoundEverywhere 𝕜` — the same capability class that
`sinTheta_unbounded_formGap_paperUINorm_rclike` already carries and for which both
source fields have instances. Producing it is a Tau Ceti roadmap question
(the roadmap currently fixes the family at `ℂ`), not a local refactor, and the
roadmap is a review surface this repository treats as read-only.

## Eventual mathematical names for the class-A objects

Their `paper` prefix is historical; none of them is Davis--Kahan vocabulary.
Recorded here so a later rename is a decision already made rather than one
rediscovered:

| object | suggested name |
| --- | --- |
| `paperProjectionBlock Ω Γ K` | `compressionBlock` — the block of `K` from `Γ` to `Ω` |
| `paperBlockCompression` | `compression` |
| `PaperSinThetaRepresentativeAcross` | `SameSingularDataAcross` — it says nothing about sines |

## Status of the migration, and what is next

The three class-C source bundles were the actionable target and all three are
done (2026-08-31): Proposition 6.1, Theorem 6.1 and Theorem 6.2 now have
canonical declarations on component hypotheses, and the records are supporting
evidence. Proposition 6.1 was the pilot, because the Challenge surface had
already demonstrated the intended direct-hypothesis API.

What that migration needed, and did not have, was a way to say *"`E₀` carries
`dom A₀` into `dom A` and `R` is the residual there"* without also saying `E₀`
is isometric. `DavisKahan1970.IsTrialResidualEquation` is that predicate, and
`isTrialResidual_iff_equation_and_isometry` ties it to the Section 2 one:

```text
IsTrialResidualEquation + IsometricEmbedding E₀   ->  Section 2 sin Θ
IsTrialResidualEquation + LowerFrameBound E₀ ε    ->  Theorem 6.1 / Theorem 6.2
```

Copying the Section 2 architecture unchanged would have strengthened Theorems
6.1 and 6.2 by requiring an isometric trial map, which is exactly the hypothesis
their lower-frame factor `ε` exists to avoid.

The remaining `C` row is `PaperUnitaryInvariantNorm`, and it stays: its
replacement is blocked at the operator-ideal layer, as recorded above.
