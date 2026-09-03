# Non-mathematical declaration names: census and rename proposal

Status: **partially_applied** — generated 2026-09-02.

**Applied from this document:**

- 2026-09-02: 83 of the 96 mechanically stale `paper` names with computable targets.
- 2026-09-02: the angle family, atomically -- 90 declarations, two-sided.
- 2026-09-02: the selected-branch tan 2Theta family -- 5 declarations.
- 2026-09-02: the plane migration and 8 module renames.
- 2026-09-02: 9 more names reached by deriving inner tokens from `Is`/`Has`-prefixed renames.
- 2026-09-02: deleted the two sine `paper*` aliases, renamed `planeE1` to `planarModelE1`, and renamed `PaperNormFanDominance.lean` and `Section9/PaperNumericalResults.lean`.

## Reviewer's recommended order

1. finish the mechanically stale `paper` theorem names (done, 83 of 96)
2. the complete angle family, atomically, as one two-sided move
3. the selected-branch tan 2Theta family, including `faithful_tanTwoTheta_uiNorm`
4. the Hilbert-Schmidt and plane migrations
5. module/file names, once the declaration API is settled
6. only then revisit the broader `source` and scaffolding census

## `paper` campaign end state

- remaining `paper` declarations: **51**
- blocked on the Hilbert–Schmidt carrier decision: 28
- remaining for review: 23

What is left is not residue. `sinTheta_paperData_complex` and `Question10_4_..._paperForm_real` are
the presentation family and wait on the marker decision; `paperSinAngleOperatorC` and
`paperDirectedSinAngleOperatorC` are the stage C sine duplicates, which are deletes rather than
renames; `unboundedSinThetaDataOfPaperCommonDomain` and `HasPaperCommonDomain` are one cluster
needing a reading of what `paper` qualifies; and three tan 2Theta corner names sit on the open
directed endpoint.

## Purpose

A census of declaration names in DavisKahan and ForTauCeti motivated by something other than the
mathematics. The `paper`-residue family HAS BEEN APPLIED; see `applied_from_this_document`. The
`source` and scaffolding families are PROPOSALS ONLY and none of them has been applied -- the
`source-provenance` family is explicitly not approved, because a reviewer produced a counterexample
to the heuristic that generated it.

## Policy

A permanent declaration name describes the mathematical object, or the hypotheses and scope that
distinguish it from a neighbouring statement. Provenance -- which paper, which section, which
campaign -- belongs in namespaces, modules, docstrings and census metadata. THE ONE SANCTIONED
EXCEPTION is a declaration that exists purely for presentation: a wrapper that bundles arguments, or
restates a theorem in display form, with no new mathematical content. Such a declaration should say
that it is a presentation, because that is the true reason it exists. The repository already has
this concept: `presentation_wrapper` is an accepted supporting-evidence role in the result
inventory, used on ten declarations.

## Method

All 11048 declaration heads in `DavisKahan/` and `ForTauCeti/` were parsed and tokenised (underscore
segments, then camelCase words), giving 1274 distinct tokens. Tokens that could indicate provenance,
review vocabulary, campaign history or scaffolding were checked against their actual declarations
rather than judged from the token alone -- which is what separated the genuine mathematics below
from the renames. Two first-draft classifications were wrong and are recorded rather than quietly
fixed: a `_source_` regex swept in `continuous_re_source` (`Continuous (re : Eℂ → E)`, domain-side)
and `compress_source_eq`, so provenance is now decided by LOCATION under `Sources/DavisKahan1970/`
plus a result tag, not by the token; and `Bridge` was miscalled scaffolding. Both are the same
failure the `paper` census made -- trusting a token to mean one thing.

## Precedent: the norm rename, completed

This is the campaign's proof that a provenance name can be replaced by the mathematical one at
scale: the structure IS a normalized symmetric norming function in dimension-coherent form, its own
docstring said so, and 446 occurrences of the mathematical name now stand where the provenance name
did. It also set the pattern this proposal follows -- the discriminating token was RENAMED
(`_paperUINorm` -> `_symmetricNorming`, 409 occurrences) rather than dropped, because it carries a
real `norm_scope` distinction against `kyFan`, `opNorm`, `uiNorm` and `idealFamily`. A
mathematically motivated name is not a shorter name.

That rename was driven off the NAMESPACE, not off the token, because 57 of its declarations carried
no `paper` token in their short names. The 144 residue names below are the mirror failure: they
carry the token but were never reached, because the first census matched only leading
`paper`/`Paper`/`IsPaper`. Neither a token grep nor a namespace walk is sufficient alone, and this
census used both.

## Summary

| measure | count |
| --- | ---: |
| declarations scanned | 11048 |
| paper residue missed by the first census | 144 |
| source total | 272 |
| source domain side mathematics keep | 88 |
| source provenance rename | 106 |
| source needs individual review | 78 |
| scaffolding declarations | 42 |
| tokens verified as mathematics keep | 8 |
| paper residue mechanical | 96 |
| paper residue presentation candidates | 8 |
| paper residue needs decision | 40 |

## Families

### `paper-residue` — RENAME (144)

**Finish the applied `paper` rename: 144 names it did not reach.**

The first census matched only leading `paper`/`Paper`/`IsPaper`, so names carrying the token after
an underscore or inside camelCase were never proposed. Stage A therefore renamed the OBJECTS but
left these names behind, and they now disagree with the objects they are about:
`adjoint_paperBlockCompression` is a theorem whose statement says `blockCompression`. The build is
green because a name is only a name, which is exactly why this needs a census rather than a
compiler.

*Rule.* Apply the stage-A map to every occurrence of a renamed object inside a declaration name, not only to
the declaration that defines it.

- **mechanical** (96) — The name references an object stage A already renamed, so the name and its own statement now disagree. `adjoint_paperBlockCompression` at TanTwoThetaUnboundedGramBridge.lean:322 states `(blockCompression Ω Γ K).adjoint = blockCompression Γ Ω K.adjoint`. Applying the stage-A map inside declaration names closes these with no new decision.

  `SameApproximationSingularSequence.paperHilbertSchmidtEnergy_eq`, `SameApproximationSingularSequence.paperHilbertSchmidtNorm_eq`, `adjoint_paperBlockCompression`, `adjoint_paperPlanarComplementMap_apply`, `adjoint_paperPlanarExactMap_apply`, `adjoint_paperScalarColumn_apply`

- **presentation candidates** (8) — `paperForm` and `PaperData` mark a declaration as the paper's presentation of a result -- `Question10_4_directed_functionalChange_paperForm_complex`, `sinTheta_generalized_paperData_complex`. These are the sanctioned exception in a different spelling, and should adopt whichever marker the reviewer settles on rather than keep a second one.

  `IsometricSinThetaPaperData`, `Question10_4_directed_functionalChange_paperForm_complex`, `Question10_4_directed_functionalChange_paperForm_real`, `RealIsometricSinThetaPaperData`, `sinTheta_generalized_paperData_complex`, `sinTheta_generalized_paperData_real`

- **needs decision** (40) — The token qualifies something stage A did not touch: `corollary3_2_paperQuarterTurn`, `HasPaperCommonDomain`, `crossedDefectEquivOfPaperDirectRotation`. Each needs a reading of what `paper` is doing -- scope marker, presentation, or genuinely nothing.

  `HasPaperCommonDomain`, `SameApproximationSingularSequence.isPaperHilbertSchmidt_iff`, `approximationEnergy_eq_paperEnergy_toReal_of_rank_le`, `corollary3_2_paperQuarterTurn`, `corollary3_2_paperQuarterTurn_symm`, `crossedDefectEquivOfPaperDirectRotation`

### `source-domain-mathematics` — KEEP — do not rename (88)

**`source` as the domain of a map is mathematics. Do not rename these.**

`source` is overloaded in this tree. In these declarations it means the domain side of an operator,
paired with `target` -- `halmosSourceDefect` against `halmosTargetDefect`,
`finiteSourceLeftSingularVector`, `finrank_source`. That is standard terminology and carries real
information. A blanket `source` rename would destroy it, which is the main reason this family is
written down.

Examples: `abs_canonicalIntertwiner_apply_eq_self_of_orthogonal_sources`, `abs_canonicalIntertwiner_apply_principalSourceVector`, `adjoint_apply_finiteSourceLeftSingularVector`, `apply_finiteSourceRightSingularBasis_eq_smul_leftSingularVector`, `apply_finiteSourceRightSingularBasis_eq_zero_of_singularValue_eq_zero`, `approximationNumber_eq_zero_of_finrank_source_le`, `approximationSingularValue_eq_finiteSourceSingularValue`, `basis_false_mem_sourceSubspace`

### `source-provenance` — NEEDS CLASSIFICATION — do not apply as a batch (106)

**`source` as `the printed form` is provenance -- but the census cannot yet tell which ones.**

Some of these genuinely mark the source-shaped statement against a stronger general theorem:
`Proposition4_2_source_compact_nonacute`, `corollary3_2_source`, `equation_9_1_source`. But the
heuristic that produced this list -- location under `Sources/DavisKahan1970/` plus a result tag --
is NOT SAFE, and a reviewer produced the counterexample: `leftCompressed_comp_source_eq`
(Section6AppendixLeakage.lean:223) is in this list and states `(Q.starProjection ∘L K) ∘L
P.starProjection = K ∘L P.starProjection`. Its `source` is the domain-side restriction along
`P.starProjection` -- the same mathematical sense as `halmosSourceDefect` on the keep-list. The
token does not distinguish the senses, and neither does the file it lives in.

*Rule.* Do not apply this family as a pass. It needs an individual target mapping per declaration and a
further semantic review. Where a name IS provenance, the repair is to name the hypotheses that make
it source-shaped -- `Proposition4_2_source_compact_nonacute` already carries them, so the token is
simply redundant there.

*Blocked on.* Individual target mappings, then semantic review. The 96 mechanical `paper` fixes were the safe
half.

Examples: `Proposition4_2_source_compact_nonacute`, `Proposition4_2_source_compact_nonacute_real`, `Theorem81SourceConclusion`, `corollary3_2_reversal_source_form`, `corollary3_2_source`, `direct_individual_vector_bounds_source`, `equation_9_1_source`, `equation_9_2_source`

### `source-needs-review` — NEEDS CLASSIFICATION — do not apply as a batch (78)

**Individual classification required.**

These use `source` outside the source-facing tree, or mix the senses: `cosTwoThetaSourceOperator`
(AngleEmbedding.lean) reads as domain-side, `beamRealModel_sourceFacts` (BeamSection9Real.lean)
reads as provenance, and `approximationNumber_paperSourceFullSinR_eq_paperCrossSineSum` is both, and
also in the paper residue. Each needs a decision; none should be renamed mechanically.

Examples: `approximationNumber_paperSourceFullSinR_eq_paperCrossSineSum`, `beamRealFiniteData_sourceFacts`, `beamRealModel_sourceFacts`, `beamRealPositiveSpectrum_sourceFacts`, `beamRealZeroMode_sourceFacts`, `commonSupSource_le_orthogonal_targetSupExterior`, `compress_source_eq`, `continuousOn_tan_sourceDirectedAngle`

### `scaffolding` — RENAME (42)

**Scaffolding words say how a proof was built, not what is true.**

Small and clearly separable. `aux` names a step rather than a statement; `_of_raw` describes the
shape of the input data; `key_identity`, `smul_compat` and
`naive_second_scalar_lower_bound_tripwire` name a proof strategy or a review device rather than a
result.

*Rule.* Name the statement. An auxiliary lemma about a norm bound is named for the bound; a `Bridge`
structure is named for the relation it carries.

*Correction.* `Bridge` was in this family in the first draft and is not scaffolding. The declarations are
`PerturbationHalfGapBridge` and `ResidualHalfGapBridge`, hypothesis-bundle structures feeding
`theorem82_branch_of_residualHalfGapBridge` -- they carry a relation, they are not migration
residue. CLAUDE.md separately sanctions `Bridge` as the established noun for an attribution-
preserving boundary (`SpectraBridge`). Left alone.

Token counts: `aux` 26, `raw` 12, `key` 1, `compat` 1, `naive` 1, `tripwire` 1

Examples: `PerturbationHalfGapBridge`, `ResidualHalfGapBridge`, `coe_realSpectrumBddSymbolsEquiv_apply_aux`, `coe_realSpectrumBddSymbolsEquiv_symm_aux`, `generalizedSinTheta_exact_of_polarData_of_raw`, `generalizedSinTheta_of_polarData_of_raw`, `gramContractionAux`, `gramContractionAux_corestrictRangeClosure`

### `presentation-exception` — MARK

**The one sanctioned non-mathematical reason: presentation.**

Some declarations exist only to present a theorem -- bundling arguments into a record, or restating
a result in display form. `sinTheta_bundled_complex` and
`proposition3_4_source_full_bundled_complex` are examples, and the result inventory already
classifies ten declarations with the `presentation_wrapper` role.

*Rule.* A presentation declaration says so in its name, and the reviewer should fix the marker.
`_presentation` is explicit and matches the inventory's existing vocabulary; `_bundled` is shorter
and already in use, but says how rather than why. Recommendation: `_presentation`, with `_bundled`
retired, so that the name states the reason the declaration exists rather than its implementation.

*Open.* Which marker, and whether presentation wrappers should additionally be required to carry the
`presentation_wrapper` role in the census so the two surfaces agree.

### `verified-mathematics` — KEEP — do not rename

**Tokens that look like review vocabulary but are mathematics. Do not sweep these up.**

Each was checked against its declarations rather than judged from the token. Recorded so that a
future pass does not 'fix' them: the naming classification's banned-token list already contains
`exact` and `generic`, which in THIS tree are usually genuine.

| token | what it means here |
| --- | --- |
| `generic` | Halmos's *generic part* of a pair of projections. `genericLeftHalf`, `genericCrossBlock`. |
| `exact` | An *exact* spectral/orthogonal decomposition, as opposed to a trial one. `IsExactSpectralDecomposition`. |
| `canonical` | The *canonical* polar factor and canonical intertwiner -- standard terms, not a status claim. |
| `final` | The *initial* and *final* projections of a partial isometry. `canonicalPolarFactor_initial_final_projection`. |
| `step` | Spectral *step* functions. `FiniteSpectralStep`. |
| `sample` | The *sample* second moment, in the statistical sense. `sampleSecondMoment`. |
| `fixed` | A *fixed* subspace of an operator. `IsFixedCosineReducingSubspace`. |
| `core` | A *core* of an unbounded operator, and common-core data. |

## Not yet decided

- The 106-name `source-provenance` pass is NOT approved and must not be applied as a batch; see that family's counterexample.
- The `source-needs-review` family (78) needs a human decision per declaration.
- The presentation marker, `_presentation` against `_bundled`.
- Whether the broader `source` and scaffolding campaign should happen at all. The reviewer's position is to finish the `paper` campaign cleanly first, on the grounds that it is already exposing architectural distinctions that will inform the decision.
