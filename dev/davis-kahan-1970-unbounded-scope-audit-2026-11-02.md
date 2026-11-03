# Davis–Kahan definitions and unbounded source scope

Initial review: 2 November 2026 against revision `018e922ed`. Independent
repair review: 2 November 2026, with the final working tree based on `7934a1b58`.
This source-to-Lean scope review follows the manuscript's Table 4 review. It
does not replace the accepted result-boundary reviews or certify the whole paper.

The initial review found an unnecessarily strong norm class and a bounded-full-
perturbation restriction in the residual alternative of Theorem 8.2. Both are
repaired in the current source-facing endpoints. The historical findings and
first repair report below are retained to explain what changed; the final
independent review records the current mathematical boundary.

## Comparison inputs

The primary source is already available locally as
`non-distributable/DavisKahan-1970-original.pdf`, with a searchable transcription
at `non-distributable/davis-kahan-1970-modernized-transcription.tex`. Neither is
needed as an additional tracked artifact. The distributable comparison surface is
[`DavisKahan1970_part_III.tex`](../prose/distilled_literature/DavisKahan1970_part_III.tex).

The comparison starts from the 29 results and their `canonical_evidence` in the
[result inventory](davis-kahan-1970-formalization-result-inventory.json), then uses
the `semantic_review`, source locators, dictionaries, and supporting declarations
in the [full census](davis-kahan-1970-full-source-census.json). Source passages are
identified below by their existing `DK-CERT` IDs. No new result or obligation is
inferred from an adjacent proof equation, example, or historical remark.

## Initial findings (superseded by the resolutions below)

### 1. Several norm quantifiers remain stronger than the source-facing boundary

Source comparison: `S1-block-residual`, `S2-unbounded-scope`, and the norm
conventions preceding the four Section 2 theorems. The source states inequalities
for arbitrary unitary-invariant norms, with a standing convention that some
results are vacuous when their displayed norms do not exist.

[`NormalizedUnitaryInvariantNorm.lean`](../DavisKahan/OperatorIdeal/NormalizedUnitaryInvariantNorm.lean)
explicitly distinguishes two records:

- `NormalizedSymmetricOperatorIdealFamily` carries Fan comparison when both
  operators belong to the norm's domain.
- `NormalizedUnitaryInvariantNorm` additionally carries unconditional Ky Fan
  dominance of the extended gauge. This transfers ideal membership from the
  right-hand operator to a majorized left-hand operator.

The stronger record's own documentation says that this membership-transfer
property is stronger than the where-defined source boundary. The conversion
`withFanDominance` requires that extra property; it does not derive it from the
weaker record.

The canonical `sinTheta_unbounded_formGap_whereDefinedUIN_rclike` and
`sinTwoTheta_commonDomain_whereDefinedUIN_rclike` use the weaker record. The
canonical tangent and double-angle tangent endpoints, `theorem5_2_sourceExact_*`,
`theorem6_1_printedGap_sourceExact_*`, `tanTheta_directed_unboundedRitz_normalizedUIN_*`,
and the norm conclusions of Theorem 8.2 still use the stronger record.

Those are valid theorems for their stated class. The binder name and older census
notes calling it the literal source norm class do not establish equivalence with
the weaker boundary now used by the sine endpoints. Their full arbitrary-norm
source-exactness claims need renewed review. This is an infinite-dimensional
norm-domain issue, independent of whether the diagonal operators are unbounded.

The existing `scaledGaugeLEWhereDefined_of_all_mul_kyFan_le` supplies a route to
weaker-boundary inequalities once the relevant Ky Fan estimates and displayed
operators are available. Transferring an inequality this way does not establish
membership of its left-hand side. Tangent representative construction and
real/complex norm transport must also be checked before declaring this repaired.

### 2. Theorem 8.2's residual endpoint still assumes bounded full perturbation

Source comparison: `DK-8.2-thm`, read with `S2-unbounded-scope` and the original
Theorem 8.2 residual proof. The source distinguishes small full perturbation from
small residual. For the latter it changes the complementary diagonal block and
uses a bounded self-adjoint completion without changing the residual or the
relevant perturbed spectral blocks.

Both residual endpoints in
[`Theorem82SourceUnbounded.lean`](../DavisKahan/Sources/DavisKahan1970/Section8/Theorem82SourceUnbounded.lean)
take `A : H →ₗ.[𝕜] H` but also `Hop : H →L[𝕜] H`. Their residual is
`sourceResidual Hop P`. Thus they cover an unbounded reference operator with a
bounded perturbation, including a perturbation whose norm is large but whose
residual is small. They do not directly accept two common-domain unbounded
self-adjoint operators whose difference has only a bounded restriction to the
reference subspace.

The current common-domain `sin 2Θ` theorem does accept that residual-only setup.
No corresponding Theorem 8.2 branch-selection endpoint was found in the Section 8
source modules. This is an interface/coverage gap for the residual-only reading
of the source's global unbounded scope, not evidence that the existing branch
theorem is false. A repair should construct the bounded self-adjoint completion
from the residual data and relate its modified reference operator to the original
one. Merely renaming the present endpoint would not cover that case.

### 3. Some registered primaries understate existing operator scope

Source comparison: `DK-6.1-prop`, `DK-6.1-thm`, and `DK-6-appendix`.

The registered `proposition6_1_printedGap_sourceExact_complex/real` take bounded
operators. The existing
`proposition6_1_commonDomain_presentation_rclike` in
[`Proposition61.lean`](../DavisKahan/Sources/DavisKahan1970/Proposition61.lean)
already gives the literal ambient sine conclusion for common-domain unbounded
self-adjoint operators with bounded difference and the two form gaps. Its norm
interface is `SymmetricNormingFunction`. The unbounded mathematics is present;
registration and norm-boundary alignment remain distinct questions.

The registered generalized sine witnesses for Theorem 6.1 accept partial maps but
use the finite interval/exterior gap. The existing `theorem6_1_sourceExact_*` in
[`Section6SourceNormClass.lean`](../DavisKahan/Sources/DavisKahan1970/Section6SourceNormClass.lean)
accept `FormBoundedSylvesterGap`, including ordered half-infinite configurations.
These broader declarations should be considered when updating canonical evidence;
their stronger norm quantifier still needs the review in finding 1.

## Definitions and source families inspected

| Source comparison | Current representation and conclusion of this review |
| --- | --- |
| Ambient self-adjoint operators | Mathlib `LinearPMap`; `IsSelfAdjoint` means equality with the partial-map adjoint, including its domain. Density and closedness follow; full domain and boundedness do not. |
| Reducing subspaces | `LinearPMap.IsReducing` preserves the operator domain under projection and requires invariance of the subspace and its orthogonal complement. It does not require the whole subspace to lie in the domain. |
| `S2-sin-theta` | Ambient operator, trial operator, and complementary exact operator are partial maps. Frames and residual are bounded maps. Trial residual equations are imposed on the trial operator's domain. Finite interval and ordered half-infinite gaps are represented. No finite-dimensional assumption. |
| `S2-tan-theta`, `DK-6.3-thm`, Appendix 6 | `UnboundedCompressionTrialData.compression` is a self-adjoint partial map. `UnboundedRitzPair` relates its domain and action to the ambient partial map. Only the residual is required bounded; neither trial compression nor ambient action is silently a bounded-map field. Complement reduction is domain-aware. Norm caveat: finding 1. |
| Ambient tangent | `HasDefinedAmbientTangent` is projection gap less than one, ensuring a bounded ambient tangent. It is separate from unboundedness of the underlying self-adjoint operators and from the directed tangent representative derived by the Ritz theorem. |
| `S2-sin-two-theta` | Canonical common-domain theorem uses two partial self-adjoint maps with equal domains. The directed clause asks only for a bounded residual extension. A globally bounded perturbation is requested separately for the ambient clause, whose right-hand side is its norm. |
| `S2-tan-two-theta` | Diagonal/reference operator is a partial map. Off-diagonal self-adjoint perturbation is bounded. Under the source's full off-diagonal hypothesis a bounded residual column determines both off-diagonal blocks and hence a bounded full perturbation. This is different from the unrestricted perturbation in finding 2. Pole exclusion is derived, not a caller-supplied extra hypothesis. Norm caveat: finding 1. |
| Section 3's eight results | Orthogonal projections, unitary rotations, and bounded angle operators are the appropriate carriers in arbitrary Hilbert dimension. The spectral-multiplicity classification includes continuous spectral data; it is not restricted to an eigenvector basis. The compact specialization is explicit. |
| Section 4's five results | Projections, rotations, and displacement are naturally bounded even when the original spectral operators are unbounded. The principal-angle extremal statements retain the source compactness setup. Proposition 4.4 is disposed of by a finite-dimensional counterexample to its universal printed claim; the proved finite-dimensional repair is a separate result. |
| `DK-5.1-thm` | Canonical Banach-space statement uses bounded coefficients as in the printed theorem. An unbounded-left-coefficient supporting wrapper exists but has an unused closedness hypothesis; the underlying bounded-inverse argument needs less. The adjacent source remark does not create a new counted result. |
| `DK-5.2-thm` | Both Sylvester coefficients are self-adjoint partial maps; solution and right-hand side are bounded, as in the source. Ordered form bounds permit both coefficients to be unbounded. Norm caveat: finding 1. |
| `DK-5.1-lem`, `DK-6.1-lem`, `DK-6.2-lem`, `DK-6.3-lem` | Cutoffs, frames, leakage operators, and residuals are bounded objects used in the unbounded proof. Their bounded carriers do not restrict the ambient diagonal operators. Rank, compactness, lower-frame, and ideal assumptions still belong to the individual lemma statements. |
| `DK-6.1-prop`, `DK-6.1-thm` | See finding 3: distinguish bounded registered witnesses and finite interval witnesses from existing broader supporting theorems. |
| `DK-6.2-thm` | Partial self-adjoint operators and the pairwise spectral gap are present. The Hilbert–Schmidt statement permits an infinite extended norm under the source vacuity convention; its rank-dependent operator-norm consequence explicitly requires a finite-rank residual. |
| `DK-8.1-thm` | Branch selection and compression inequalities have unbounded ambient forms. Compression comparisons are quadratic-form inequalities on the appropriate domains. The printed finite-dimensional eigenvalue/gauge clauses have explicitly finite-dimensional witnesses. |
| `DK-8.2-thm` | Unbounded reference operator, but bounded full perturbation in both alternatives; see finding 2. Bounded reference compression is derived from its spectrum lying in the stated finite band, rather than imposed as a separate caller assumption. Norm caveat: finding 1. |

Theorem 8.1(ii) also mentions natural infinite-dimensional extensions. Its
finite-dimensional eigenvalue declarations alone do not certify a particular
infinite-dimensional enumeration. The unbounded compression inequalities are
present; the precise interpretation of that additional source phrase remains a
boundary question, rather than a reason to invent an unspecified new theorem.

## Verification and census maintenance observations

The existing alignment renderer was run with compiler probes for the four
Section 2 families, Theorems 5.1 and 5.2, Proposition 6.1, Theorems 6.1–6.3,
and Theorems 8.1–8.2. Local output:
`/tmp/dkps-unbounded-census-review.md`. It exposed stale supporting/dictionary
references: `TauCeti.LinearPMap.ReducesSubspace` (current predicate:
`LinearPMap.IsReducing`), unqualified `CompatibleCrossOperatorNorm`, and
`TauCeti.opNorm_spectralSubspace_sub_le`. These are lookup failures, not failed
proofs of the registered canonical statements. The last reference belongs to
the additional projector-difference review variant, outside the 29-result list.

A separate temporary Lean probe imports `DavisKahan.All`, checks all 76 distinct
canonical declaration names from the inventory's 78 evidence entries, prints the
key structures, and prints axiom dependencies of the sine, double-angle sine,
directed tangent, and residual Theorem 8.2 witnesses. It passes with the standard
axioms and no `sorryAx`. Local files:
`/tmp/DkpsUnboundedScopeAudit.lean` and `/tmp/dkps-unbounded-scope-compiler.log`.
This validates elaborated types and dependencies, not semantic source equality.

The older census contains historical closure claims as well as later repairs.
Neither an old `accepted` label nor successful declaration resolution discharges
the norm-boundary and residual-only scope questions above. This review leaves the
29-result selection and existing certificates unchanged; it records challenges
to source-scope acceptance, without pretending to have repaired the proofs or
recertified the paper.

## Follow-up: Theorem 8.2 repair route

The user prioritizes removing the bounded-full-perturbation restriction in 8.2;
the stronger norm assumption is recorded for later repair. Stronger conclusions
or weaker hypotheses in an existing theorem are acceptable evidence. The norm
issue above is specifically an additional hypothesis, rather than a stronger
conclusion.

Inspection of `Theorem82UnboundedPath.lean` and
`ForTauCeti/Analysis/InnerProductSpace/Polar/SelfAdjointCompletion.lean` gives a
concrete reduction using existing mathematics:

1. Start with common-domain self-adjoint reference and perturbed operators
   `A,T`, a reducing reference subspace `P`, and bounded residual `R`.
   The finite spectral band of `A|P` gives `P ⊆ dom A = dom T` and a bounded
   realization of `A|P` using the existing bounded-spectrum theorem.
2. Write `Π` for the orthogonal projection onto `P`, and `C = R ∘ Π` for
   the residual extended by zero on `Pᗮ`. Symmetry of `T-A` on `P` implies
   `ΠC = C*Π`. Consequently `K₀ = C + C* - ΠC` is bounded self-adjoint and
   agrees with `R` on `P`.
3. Apply the existing `exists_selfAdjoint_completion_eq_norm_restriction`
   to `K₀`. This supplies a bounded self-adjoint `K` agreeing with `R` on
   `P`, with `‖K‖ = ‖R‖`. No assumption that `T-A` is globally bounded is
   needed to construct `K₀` or `K`.
4. Set `A' = T-K`. Bounded perturbation preserves self-adjointness and
   domain. On `P`, `A'` equals `A`, so `P` reduces `A'` and its reference
   spectral band is unchanged. The perturbed operator is still exactly
   `T = A'+K`, so its `Q` blocks and their spectral gap are unchanged.
5. The existing perturbation alternative gives the acute branch because
   `‖K‖ = ‖R‖ < δ/2`. The existing common-domain directed `sin 2Θ` theorem
   supplies the retained inequality with the original residual.

This is a proposed conventional proof, not a new compiler-certified result.
The homotopy and sharp completion arguments already exist. The main remaining
Lean work is the residual-column symmetry bridge, reduction/restriction
equalities for `A'`, and the real-scalar transport. A few hundred lines and a
focused implementation session are a reasonable preliminary estimate; the
domain transport must compile before calling the gap closed.

For the census-only findings, broader evidence already exists for Proposition
6.1 and Theorem 6.1. Updating the selected witnesses and their clause mappings
does not need new spectral mathematics. Keep the old printed-scope witnesses
available and distinguish the broader operator scope from the norm-interface
qualification; successful repointing alone cannot repair Theorem 8.2.

## Resolution, 2 November 2026

The operator-scope limitations identified in findings 2 and 3 are repaired.
The historical findings above describe the state before this implementation.

`DavisKahan/Sources/DavisKahan1970/Section8/Theorem82CommonDomain.lean` proves:

- `TauCeti.DavisKahan1970.Section8.theorem8_2_residual_commonDomain_normalizedUIN_complex`;
- `TauCeti.DavisKahan1970.Section8.theorem8_2_residual_commonDomain_normalizedUIN_real`;
- `TauCeti.DavisKahan1970.Section8.theorem8_2_residual_commonDomain_fullAngle_lt_complex`;
- `TauCeti.DavisKahan1970.Section8.theorem8_2_residual_commonDomain_fullAngle_lt_real`.

The first two accept common-domain self-adjoint partial maps `A,T` and a bounded
residual `R` on the reducing reference subspace. They conclude both the retained
directed double-angle inequality and the literal ambient angle below pi/4. The
last two give the acute branch without any ideal-norm premise. No theorem in
this family assumes a globally bounded full difference `T-A`. The compact
reference spectral band supplies the trial-domain and Ritz realization data.
The complex completion has norm exactly `||R||`; real-part descent also gives an
exact-norm real completion. The construction then uses `A'=T-K`, preserving the
reference restriction and the perturbed spectral blocks.

The result inventory, clause primaries, full census, and statement-map review
lists now select those witnesses. The perturbation alternative is unchanged;
older bounded-perturbation residual/branch declarations remain supporting
specializations. Theorem 8.2's acute clause is recorded separately for each
smallness alternative and scalar field.

Proposition 6.1 now selects
`TauCeti.DavisKahan1970.proposition6_1_commonDomain_normalizedUIN_rclike`, a small
wrapper around the existing unbounded common-domain literal-sine theorem with
the same normalized-norm interface as before. Theorem 6.1 selects its existing
`TauCeti.DavisKahan1970.theorem6_1_sourceExact_complex/real` declarations, whose
full form-gap predicate includes the ordered half-infinite configurations.
These Section 6 witnesses also allow nonseparable ambient Hilbert spaces;
the former bounded/printed-gap witnesses remain supporting specializations.
No counted result, source atom, or accepted statement boundary changed.

At this first operator-scope checkpoint, finding 1 was deferred at the user's
direction. The user subsequently requested the norm repair explicitly. The final
independent review below supersedes that temporary deferral and the stronger
canonical norm interfaces described in this checkpoint.

Validation: the focused Lake build of the new Theorem 8.2 module and Section 6
norm module passed, followed by `lake build DavisKahan.All` (10,962 jobs). The
existing result-inventory checker passed with compiler probes. These checks
establish compilation and registered types; they do not establish that every
remaining arbitrary-norm source-scope issue is repaired.

The full maintained `ResultSemanticSurface.lean` also compiles. Explicit axiom
probes for all five new public declarations report only `propext`,
`Classical.choice`, and `Quot.sound`. The statement-map check passes after
refreshing its existing generated audit template. The two repaired rows with
semantic-review packets (`DK-6.1-thm`, `DK-8.2-thm`) pass the existing alignment
renderer with compiler probes, and their statement pins were refreshed using
`aiq-lean alignment pin`. Multiline `#check` commands in the audit surface were
put on one line so the existing inventory check recognizes their declarations;
no checker implementation was changed.

Broad static census validation still reports ten declaration lookups in other
rows: one in `S1-ui-norms`, four in `S2-sharpness`, three in `DK-3.2-def`, and
two in `DK-3.5-prop`. These references were unchanged by this repair. The focused
result-inventory and repaired-row compiler checks pass independently; the broad
static census validation is not reported as passing.


## Final independent review and norm repair, 2 November 2026

### Common-domain residual branch and Proposition 6.1

The independent comparison used the actual Theorem 8.2 on original PDF page 37,
Proposition 6.1 on page 26, and the unbounded Appendix passage on page 30, together
with the census source boundaries. Compilation was checked separately from that
comparison. No additional operator/domain defect was found in the first repair.

The new common-domain residual proof constructs the symmetric column extension
`C+C*−ΠC`, applies the sharp complex self-adjoint completion theorem, and descends
the real case by real parts. Its completion agrees with the original residual
and has exactly its norm. The modified reference `A'=T−K` is self-adjoint on the
same domain, agrees with the original reference on its reducing band, and leaves
the perturbed operator and both perturbed spectral blocks unchanged. The finite
reference band supplies the required full trial domain and bounded reference
restriction; neither is an extra caller hypothesis. The original difference
`T−A` is allowed to be unbounded away from the reference subspace.

The standing crossed-defect assumption is retained. The two smallness
alternatives retain the appropriate ambient or directed double-angle bound and
the literal full-angle conclusion below π/4. The common-domain norm-free acute
corollaries require neither ideal membership nor a norm object. Proposition 6.1
uses both form gaps on common-domain self-adjoint partial maps; Theorem 6.1 uses
`FormBoundedSylvesterGap`, including the ordered half-infinite configurations.
Dropping separability is a weakening of hypotheses, whereas the old stronger norm
record was an additional hypothesis and required a separate repair.

### Weaker norm boundary

The canonical declarations for 11 result rows are now retargeted to 26 distinct
where-defined norm endpoints: the two tangent families, Corollary 4.1,
Proposition 4.3, Theorem 5.2, Lemmas 6.1–6.2, Proposition 6.1, Theorems 6.1 and
6.3, and Theorem 8.2. The sine and double-angle sine endpoints already used this
weaker family. The result count and all accepted statement boundaries remain
unchanged. Adjacent definitions, proof equations and sharpness commentary remain
classified source material, without new proof obligations.

`Ideals/WhereDefinedNormTransfer.lean` reuses the existing Ky Fan estimates and
`scaledGaugeLEWhereDefined_of_all_mul_kyFan_le`. Each numerical inequality takes
`NormalizedSymmetricOperatorIdealFamily` and membership of **both** displayed
operands. It does not assume the weak norm's domain is closed under arbitrary
singular-value majorization, and does not claim such membership transfer.
`NormalizedUnitaryInvariantNorm` endpoints remain useful stronger-assumption
membership-transfer results, separately registered as supporting evidence.

The weaker family still explicitly carries its where-defined Fan comparison
law. This repair does not prove a representation theorem deriving that law from
bare unitary invariance alone. It aligns the affected endpoints with the same
norm boundary already adopted by the source-facing sine theorems.

The directed tangent pole exclusion and representative construction are
independent of the norm object. Canonical directed tangent and tan(2Θ) conclusions
use the actual functional-calculus operators. In particular, the real directed
tan(2Θ) theorem compares a real operator with a real block residual under one
real weak norm family. It does not require an arbitrary real norm family to
extend to the complexification. The older complexified corner correspondence
remains supporting proof evidence rather than a hypothesis on the literal
source endpoint. Ambient tangent keeps its existing definedness semantics.

Lemma 6.1's quantified premises were also repaired: they range over weak norm
families with both displayed membership conditions. The converse recovers
uniform finite Ky Fan comparisons before invoking the stronger output norm's
membership-transfer law. This avoids silently retaining the stronger norm class
inside a quantified hypothesis. Section 8.2's weak numeric comparison is
conditional on both memberships, while its angle conclusion is unconditional
on those memberships.

### Reference maintenance

The ten apparent missing lookups comprised six retired names and four accepted
upstream declarations omitted by the local-only static scan. The valid
`LinearMap.exists_orthonormal_sum_inner_eq_kyFanSum`, `Submodule.IsAcute`,
`Submodule.IsAcute.of_projectionGap_lt_one`, and
`Submodule.directedProjectionGap_lt_one_iff` are preserved. Compiler lookup,
rather than a local source-tree scan, verifies them.

The six genuine stale references now use the accepted WithLp product-isometry
and two-sided-unitary-orbit singular-value APIs, symmetric CFC intertwining,
`LinearMap.prodMap`/`withLpMap` with definitional subtraction compatibility,
`LinearMap.moorePenroseInverse_adjoint` plus symmetric adjoint equality, and
`Submodule.starProjection_orthogonal`. Their row explanations record the
representation changes. Definitions and source commentary retain their original
roles. No similarly named result was substituted without checking its type.

### Validation and limits

- `lake build DavisKahan.All` passed (10,972 jobs), including existing stronger
  short-name clients in `SectionTwoUsage`.
- The maintained `ResultSemanticSurface.lean` compiled. An explicit probe of all
  26 canonical weak endpoints and eight Section 2 aliases compiled; the 26 axiom
  reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
- The existing inventory checker passes with compiler probes and
  `--require-terminal`; the statement-map check passes with the same flag.
  Full census metadata validation reports no findings. Its complete compiler
  probe resolves all 1,577 registered declarations with zero unresolved names.
  The generated reviewer packet is a regenerable ignored output; authored Lean
  audit wrappers and mathematical reviews remain source evidence.
- The existing alignment renderer elaborated all affected row comparisons with
  the refreshed statement pins. The selected directed tan(2Θ) declarations now
  state the literal operator, so obsolete required corner-to-literal bridge
  metadata was demoted to supporting evidence. No checker was weakened.

These checks establish elaboration, declaration resolution and trusted axiom
usage. The source comparison and norm/domain interpretation above are the
independent mathematical review; neither a green build nor a self-consistent
census is, by itself, a new full-paper completion claim.
