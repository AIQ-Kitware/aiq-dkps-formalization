# Hostile review of the Davis--Kahan 1970 formalization — 2026-09-04

**Reviewer:** Claude Opus 5, single session, commit `ba8a72fe` (main; the Lean tree and the
`dev/*.json` ledgers are identical to `33fddbd4`).
**Mandate:** attack the 29/29 claim in `dev/davis-kahan-1970-formalization-result-inventory.json`
following `dev/davis-kahan-1970-independent-audit-prompt.md` (Passes A, B, C), and report
naming/placement defects opportunistically.
**Materials read:** the distributable TeX (Sections 1--8 in full), the 29-result inventory
(every row; full row text for S2-tan-theta, DK-3.1-thm, DK-4.1-prop, DK-4.1-cor, DK-4.4-prop,
DK-5.1-lem, DK-6.3-thm, DK-8.1-thm, DK-8.2-thm, S2-sin-two-theta), the source-atom inventory
dispositions for the blocks named below, the compiler-printed types of ~90 source-facing
declarations (from a fresh build of `Audits/ResultSemanticSurface.lean`), and the Lean
definitions every one of those types rests on (`FormBoundedSylvesterGap`,
`SymmetricNormingFunction`/`Mem`/`gauge`, `realSpectrum`, `IsTrialResidual`,
`IsExactSpectralDecomposition`, `UnboundedTrialBlock`, `UnboundedRitzPair`,
`UnboundedCompressionTrialData`, `ReducingComplement`, `ReflectionIntertwines`, `IsOddFor`,
`reflectionPerturbation`, `HasDefinedAmbientTangent`,
`HasTheorem63DirectedTangentApproximationNumbersInfinite`, every `Angle.*` object,
`sinTwoThetaIdealBlock`, `projectorDifference`/`doubleSecant`, `IsAcute`, `IsDirectRotation`,
`CrossedDefectsEquivalent`, `CrossedDefectsSameDimension`, `SameSpectralMultiplicity`,
`SameSpectralMultiplicityAwayFromZero`, `SameHalmosTrivialDimensions`,
`IsPrincipalUnitarySquareRoot`, `spectraReflectionProduct`, `IsPrintedFixedCosineReducingSubspace`,
`SylvesterEquation`, `CompatibleCrossOperatorNorm`, `HasApproximationNumberStrongCutoff`,
`Theorem81Conclusion`, `canonicalLowBranch`, `maximalAngle`, `DavisKahanProposition4_4_Finite`
and its witness).

## Verdict

**The 29/29 claim survives as a claim about the mathematics in the tree, with two
qualifications the inventory does not currently state, and it does not survive unqualified as
a claim about what the registered canonical evidence says.**

* Every one of the 29 counted results has compiled, `sorry`-free, standard-axiom Lean evidence.
  For 26 of them the registered canonical declarations state the printed result at the printed
  scope or a strictly weaker-hypothesis form of it. I found **no false registration** — no row
  whose evidence proves something other than (a consequence-equivalent of) the printed result.
* **F1 (first-order, registration):** the canonical witnesses of **DK-6.3-thm** carry a
  hypothesis the printed Theorem 6.3 does not impose (a spectral gap of the perturbed operator
  in `(α, α+δ)`, equivalently that the reducing subspace `Q` *is* the spectral subspace below
  `α`). The row's own `source_clauses.justification` records the extra hypothesis and the row
  is nevertheless marked `locally_exact` / `proved_exact`. The printed-shape theorem exists in
  the tree (`tanTheta_directed_unboundedRitz_symmetricNorming_{complex,real}`) but is
  registered only under S2-tan-theta. A concrete 4x4 instance of the printed theorem that the
  registered witnesses do not cover is given below.
* **F2 (first-order, scope accounting):** **DK-8.1-thm** and **DK-8.2-thm** are formalized for
  *bounded* `A, H : E →L[ℂ] E` only. Their printed hypotheses are "the hypotheses of the
  tan 2θ theorem" and "the hypotheses of the sin 2θ theorem", and the repository's own
  source-fidelity model links the unbounded-scope atoms `S2-unbounded-scope.*` to *all four*
  Section 2 results as `result_scope`. By the repository's own reading, Section 8 inherits
  unbounded scope and is delivered at bounded scope, and neither row discloses the restriction.
* Everything else I found is a statement-honesty, naming, placement or tooling defect
  (F3--F9). None of them changes what is proved; several of them change what a reader can
  *see* is proved without opening a proof.

Pass A (selection) is accepted. Pass C (nonlocal interpretations) passes on all five rows,
with the reservation on S2-tan-theta recorded under F3.

## Mechanical checks performed

| check | result |
| --- | --- |
| `grep -w sorry` over `DavisKahan/`, `ForTauCeti/` | 0 files |
| `axiom` declarations in the two libraries | none (one docstring use of the word) |
| `lake build DavisKahan.Sources.DavisKahan1970.Audits.ResultSemanticSurface` | success, 342 `#check`s, 0 warnings |
| `#print axioms` on the 8 `SectionTwo` endpoints, the Prop 4.4 refutation, both Theorem 3.1 directions, `theorem8_2_branch_maximalAngle_lt_of_crossedDefects`, `Lemma5_1`, `tanTheta_directed_unboundedRitz_symmetricNorming_complex`, `crossedDefectsEquivalent_iff_sameDimension` | `[propext, Classical.choice, Quot.sound]` only |
| `scripts/certify_davis_kahan_1970.py --require-terminal` | every step passes (1247/1247 registered declarations resolve; 29/29 terminal; 48/50 census rows proved, 2 n/a; signature probe 1247/1247) but **`overall_status: FAIL`**, because `DavisKahan.All` emits 81 warnings and the gate refuses warnings; see F8 |
| Prop 4.4 refutation, independent numerical check | see F10 |

## Findings, ranked

### F1 — DK-6.3-thm: canonical witnesses are a proper specialization of the printed theorem

**Printed (TeX, DK-6.3-thm):** `E₀,E₁,F₀,F₁` exhaustive isometries whose ranges reduce `A`
and `A+H`; `dim X(E₀) < dim X(F₀)` allowed; `A₀ = E₀*(A+H)E₀`; `R` by (1.8);
`spec(A₀) ⊂ [β,α]`, `spec(Λ₁) ⊂ [α+δ,∞)`. Conclusion `δ‖tan Θ₀‖ ≤ ‖R‖` for every UI norm.
**Nothing is assumed about `Λ₀`.** `Q = Ran F₀` is any reducing subspace of `A+H` whose
complementary block is `≥ α+δ`.

**Registered canonical evidence:** `tanTheta_directed_unboundedTrial_symmetricNorming_{complex,real}`.
Compiler-printed hypotheses (complex):

```
(hA : IsSelfAdjoint A) (D : UnboundedTrialBlock A Z) (0 < δ)
specProjection hA (Set.Ioo α (α + δ)) _ = 0
(∀ z : Z, re ⟪D.operator z, z⟫ ≤ α ‖z‖²)
HasTheorem63DirectedTangentApproximationNumbersInfinite Z (selfAdjointSpectralSubspace A hA (Set.Iic α) _) tanTheta0
N.Mem D.residual
```

So the Lean theorem (i) assumes the perturbed operator has **no spectrum in `(α, α+δ)`** and
(ii) compares the trial subspace with the **spectral subspace of `A+H` below `α`**, not with
an arbitrary reducing `Q` whose complement is coercive. The row's `source_clauses.justification`
says exactly this ("no spectrum of A in (α, α + δ)") and still records the clause as
`established` under `semantic_alignment: locally_exact`.

**Instance of the printed theorem outside the registered hypothesis.** In `ℂ⁴` let
`T = A+H = diag(−1, 1/2, 1, 1)`, `α = 0`, `δ = 1`, `Q = span(e₁,e₂,e₃)` (so
`Λ₁ = T|span(e₄) = 1 ≥ α+δ`, `Λ₀ = diag(−1, 1/2, 1)`), trial vector
`x = (e₁+e₄)/√2`, `A₀ = ⟨Tx,x⟩ = 0 ≤ α`, `H₀ = 0` by the Rayleigh--Ritz choice.
The printed theorem applies and gives `1·tan(π/4) = 1 ≤ ‖R‖ = 1` (sharp).
`specProjection T (Ioo 0 1) ≠ 0` because `1/2 ∈ spec T`, so neither registered witness
applies; the best they give is at `α' = 1/2, δ' = 1/2`, i.e. `1/2 ≤ 1`, which is a strictly
weaker statement. The gap cannot be closed by re-choosing `α, δ` when `Λ₀` has spectrum
accumulating at `α` from above.

**The printed-shape theorem exists.** `tanTheta_directed_unboundedRitz_symmetricNorming_complex`
takes `UnboundedRitzPair A Z`, `ReducingComplement A V` (arbitrary `V` whose complement
reduces `A`), coercivity `(α+δ)‖y‖² ≤ re⟪Ay,y⟫` on `Vᗮ ∩ dom A`, `SemiboundedAbove
D.trial.compression α`, and concludes on a representative characterized against `V`. That is
Theorem 6.3's hypothesis shape (and the Appendix's unbounded-Ritz strengthening). It is
registered under S2-tan-theta only. `Section2.theorem6_3_perturbation_infiniteTrial` has the
same shape at bounded scope over a `KyFanDominantIdealFamily`.

**Repair (cheap):** make `tanTheta_directed_unboundedRitz_symmetricNorming_{complex,real}`
the canonical evidence of DK-6.3-thm (they also cover `dim X(E₀) < dim X(F₀)` since `Z` is
arbitrary), demote the `_unboundedTrial_` pair to `specialization`, and rewrite the two
`source_clauses.justification` strings, which currently describe the wrong hypothesis as
established. Also rename: the `_unboundedTrial_` pair should carry `spectralGap` in the name
the way `tanTheta_directed_bounded_spectralGap_*` already does — the name currently hides the
narrowing that the bounded sibling's name discloses.

### F2 — DK-8.1-thm and DK-8.2-thm are delivered at bounded scope under an inherited unbounded reading

Every registered Section 8 declaration takes `A H : E →L[ℂ] E` (or `→L[ℝ]`). The paper's
Theorem 8.1 opens "Assume the hypotheses of the tan 2θ theorem"; Theorem 8.2 opens "Add to the
hypotheses of the sin 2θ theorem". The repository's fidelity model attaches
`S2-unbounded-scope.unbounded-selfadjoint-scope`, `.bounded-residual-needed`,
`.half-infinite-gap-intervals` and `.infinite-dimensional-scope` as `result_scope` to
**S2-tan-two-theta and S2-sin-two-theta**, and both of those rows are certified with
`LinearPMap` endpoints. The same inheritance mechanism that makes those rows unbounded makes
Section 8's hypotheses unbounded, and DK-8.1-thm / DK-8.2-thm are `locally_exact`,
`proved_exact`, with no scope atom, no boundary note and no `review_note` sentence saying
"bounded". The only Section 8 clauses the paper itself restricts are 8.1(ii) ("in finite
dimensions, with natural infinite-dimensional extensions") and 8.1(iii) (finite-dimensional
gauges), and those are correctly delivered (`upperApproximationRepulsion` in approximation-number
form, `upperSymmetricGaugeRepulsion_angle_rev` with `[FiniteDimensional]`).

This is a consistency defect in the scope accounting, not a claim that the paper demands
unbounded Section 8 theorems. Two honest resolutions: (a) add an accepted `boundary_review`
decision on both rows stating that Section 8 is read at the bounded main-body scope and why
(the source's Section 8 proofs are written for bounded operators, and the S2 unbounded passage
names only Theorem 5.2 and the Appendix to Section 6 as the unbounded machinery), or (b) lift
the iff `theorem8_1_maximalAngle_le_iff_spectrumIn`, part (i), and the Theorem 8.2 branch
theorem to a `LinearPMap` ambient with bounded `H`, which the existing unbounded sin 2θ / tan 2θ
endpoints already have the vocabulary for (`ReducesSubspace`, `IsOddFor`, form bounds on
`dom A`). Option (a) is a one-day census edit; option (b) is real work. Either is acceptable;
the current state — silence — is not.

### F3 — Junk-valued functional calculus in conclusions (statement honesty, not mathematics)

Mathlib's `cfc f a` is `0` whenever `f` is not continuous on `spectrum ℝ a`, and `Real.tan` is
total with `tan (π/2) = 0`. The tree defines

* `tanAngleOperatorC U V := cfc Real.tan (angleOperatorC U V)` — equals `0` when
  `π/2 ∈ spectrum Θ`;
* `absTanTwoAngleOperatorC U V := cfc (fun t => |Real.tan (2t)|) (angleOperatorC U V)` —
  equals `0` when `π/4 ∈ spectrum Θ`;
* `HasTheorem63DirectedTangentApproximationNumbersInfinite Z V T :=
  ∀ n, aₙ(T) = Real.tan (Real.arcsin (aₙ(P_{Vᗮ}|_Z)))` — at a right principal angle
  (`aₙ = 1`) this *requires* `aₙ(T) = 0`, so a right angle forces the "tangent representative"
  to be the zero operator.

Consequently a conclusion of the form `N.Mem (tanAngleOperatorC U V) ∧ δ N(tanAngleOperatorC U V) ≤ N(H)`
is trivially true precisely in the case the paper's proof rules out, and nothing *in the type*
distinguishes the two situations. The repository knows this — the `HasDefinedAmbientTangent`
docstring says so verbatim — and handles it honestly for the *definedTangent* endpoints, which
take `π/2 ∉ spectrum Θ` as a hypothesis (with the biconditional
`hasDefinedAmbientTangent_iff_pi_div_two_notMem_spectrum`). It does **not** expose it for:

1. the (3.5)-form ambient tan θ endpoints
   (`tanTheta_ambient_unboundedRitz_symmetricNorming_*`,
   `tanTheta_ambient_unboundedRitz_explicitCompatibility_symmetricNorming_*`,
   `tanTheta_ambient_unboundedOperator_boundedRitz_symmetricNorming_*`,
   `tanTheta_ambient_bounded_symmetricNorming_*_of_crossedDefects`). Their proofs *do*
   establish uniform transversality first
   (`norm_sinAngleOperatorC_lt_one_of_crossedDefectsEquivalent`, TanThetaAmbient.lean) — so
   the theorems are non-vacuous — but the docstring claim "the (3.5) endpoints remain as the
   non-vacuous corollary" is not certified by any type. Add `HasDefinedAmbientTangent U V`
   (equivalently `‖sinAngleOperatorC U V‖ < 1`) as a conjunct of the conclusion; it is already
   in hand inside every proof.
2. the ambient tan 2θ endpoints `tanTwoTheta_ambient_unbounded_symmetricNorming_*`. The
   `blockRepresentative_derivedReflection` form concludes
   `IsUnit (diagonalPart …)²` as its first conjunct — the pole certificate — and the
   angle-operator form drops it. Restore it as `∀ t ∈ spectrum ℝ (angleOperatorC P V), cos (2t) ≠ 0`
   (this is exactly `cos_two_ne_zero_of_isUnit_diagonalPart_reflection_sq`, already applied
   inside the proof). The **directed** tan 2θ clause is honest here: it concludes
   `∀ n, aₙ(sinTwoThetaIdealBlock U V) < 1`, and `a₀` is the norm, so the pole is uniformly
   excluded by the type.
3. the directed tan θ endpoints (`tanTheta_directed_unboundedTrial_*`,
   `tanTheta_directed_unboundedRitz_*`, `theorem6_3_unbounded_infiniteTrial_ideal*`). The
   paper's Appendix explicitly obtains "a uniform positive lower bound for the relevant
   cosines"; the infrastructure proves it
   (`approximationSingularValue_sineBlock_lt_one_infiniteData`, for every `n` including
   `n = 0`, hence `‖P_{Vᗮ}|_Z‖ < 1`); the endpoints do not state it. Add
   `‖theorem63DirectedSineBlock Z V‖ < 1` to the conclusion, after which the
   `tan ∘ arcsin` characterization is manifestly junk-free.

The same audit found the sine-side objects clean: `sinAngleOperator` is a modulus,
`angleOperatorC = cfc arcsin (…)` with `arcsin` continuous, `sinTwoAngleOperatorC` uses
`sin (2t)`, and `directedSinTwoAngleOperator` is a product of moduli — no totalization
anywhere in the `sin Θ` / `sin 2Θ` conclusions.

### F4 — DK-5.1-lem: the registered `Lemma5_1` is the lemma assumed as a typeclass

```
TauCeti.DavisKahan1970.Lemma5_1 : ∀ {𝕜} [RCLike 𝕜] … [HasApproximationNumberStrongCutoff 𝕜] …
```

`HasApproximationNumberStrongCutoff 𝕜` is a `class` whose **only field is the statement of
Lemma 5.1** (`ScalarGeneric.lean:60`). At `ℝ` and `ℂ` it is discharged by the instances
`realHasApproximationNumberStrongCutoff` / `complexHasApproximationNumberStrongCutoff`, whose
fields are the genuine proofs `ApproximationNumbersReal.approximationSingularValue_comp_strongProjection_tendsto_real`
and `approximationSingularValue_comp_strongProjection_tendsto_complex`. Neither of those is
registered on the row; the sole registered witness is a wrapper of the form "given Lemma 5.1,
Lemma 5.1". This contradicts the repository's own rule that proof-vehicle capability classes
must not appear in source-facing signatures, and a reader of the census cannot tell from the
row that the lemma is proved rather than assumed. Register the two field proofs as the real
witnesses (scalar scope `real`/`complex`), keep `Lemma5_1` as the generic facade if wanted, and
say so in the row.

### F5 — S2-sin-two-theta, ambient clause: canonical evidence narrows the paper's arbitrary reducing `P` to a spectral subspace

The printed ambient conclusion `δ‖sin 2Θ‖ ≤ 2‖H‖` takes `P` to be *any* reducing subspace of
`A` (Section 1: "Let `P` reduce `A`"); under the gap hypothesis `Q` is necessarily the spectral
subspace of `A+H` on `[β,α]`, but `P` is not constrained. The canonical evidence
`sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_{complex,real}` (and the alias
`SectionTwo.sinTwoTheta_ambient_*`, and the "both conclusions" certificate) take the
non-gapped side as `selfAdjointSpectralSubspace (A.addBounded Eop) S` for a measurable `S`.
Reducing subspaces of a self-adjoint operator are not all spectral (any subspace reduces
`A = 0`), so this is a proper specialization. The printed shape is proved in the tree by
`sinTwoTheta_ambient_unbounded_reflectionPair_symmetricNorming_rclike`, whose `V` is
arbitrary and whose intertwining hypothesis unfolds exactly to "`V` reduces `A + Eop`"
(`reflectionPerturbation V Eop = Eop − X_V Eop X_V`). That theorem is registered on the row
but is not canonical evidence and is not what the presentation module tells a reader to cite.
Promote it (or a fixed-field alias of it) to canonical evidence for the ambient clause; the
spectral-subspace endpoints remain as specializations. The **directed** sin 2θ clause has no
such problem (`V` arbitrary, `M` arbitrary), and the bounded Section 8 forms already take
`A.Reduces P`.

### F6 — Naming and placement defects (report requested by the user)

1. **Root-namespace leak.** `DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean`
   opens `namespace DavisKahan1970` without `TauCeti`. Eight registered declarations live there,
   including the sin θ *theorem to cite*
   (`DavisKahan1970.sinTheta_unbounded_formGap_symmetricNorming_rclike`), `isTrialResidual_iff`,
   `isExactSpectralDecomposition_iff`, and the predicates `IsTrialResidual`,
   `IsTrialResidualEquation`, `IsExactSpectralDecomposition` that appear in the *types* of
   `TauCeti.DavisKahan1970.theorem6_1_complex` and `theorem6_2_complex`. The `SectionTwo.sinTheta`
   alias re-exports it under `TauCeti.…`, which hides rather than fixes the misplacement.
   Every other source-facing module is under `TauCeti.DavisKahan1970`. Move it.
2. **Six case-twin pairs registered on the same rows**, differing only in capitalization and
   meaning different things (record-method alias vs. component theorem):
   `Proposition6_1_complex`/`proposition6_1_complex`, `Proposition6_1_real`/`proposition6_1_real`,
   `Theorem6_1_complex`/`theorem6_1_complex`, `Theorem6_1_real`/`theorem6_1_real`,
   `Theorem6_2_complex`/`theorem6_2_complex`, `Theorem6_2_real`/`theorem6_2_real`. The module's
   own comment says the lowercase ones are canonical and the capitalized ones are
   "implementation and compatibility API". Deregister the capitalized ones from the census (or
   rename them `*Data.result…`), and do not let two names that differ only in case coexist.
3. **Section-inconsistent casing of source-facing names.** Section 3 and Section 8 use
   `proposition3_1`, `theorem3_1_*`, `corollary3_2`, `theorem8_1_*`; Section 4 and 5 use
   `Proposition4_1_*`, `Corollary4_1_*`, `Proposition4_3_*`, `Theorem5_2`, `Lemma5_1`;
   Section 6 has both. Pick one (the lowercase `theoremN_M_*` form is what the
   naming-classification file commits to) and apply it.
4. **Source-facing witnesses outside the source namespace.**
   `TauCeti.DavisKahan.TanTheta.theorem6_3_unbounded_infiniteTrial_ideal_exists` is registered
   evidence living in `DavisKahan/TanTheta/` under `DavisKahan.TanTheta`;
   `TauCeti.DavisKahan.Section2.theorem6_3_perturbation_infiniteTrial` lives in
   `Sources/DavisKahan1970/Section2TanThetaPerturbation.lean` but in the namespace
   `DavisKahan.Section2` rather than `DavisKahan1970` (a Theorem-6.3 declaration in a
   `Section2` namespace, outside the paper namespace). Similarly
   `TauCeti.DavisKahan.Sylvester.davisKahan1970_sylvester_real` on DK-5.2-thm and
   `TauCeti.DavisKahan.FiniteDimensional.DavisKahanProposition4_4_Finite` (capitalized Prop-valued
   `def`, `FiniteDimensional` namespace) on DK-4.4-prop. Either give these source-facing aliases
   in `Sources/DavisKahan1970/` or record them as `implementation_structure`, not witnesses.
5. **Names that hide a hypothesis their sibling's name discloses.**
   `tanTheta_directed_bounded_spectralGap_symmetricNorming_*` says `spectralGap`;
   `tanTheta_directed_unboundedTrial_symmetricNorming_*` carries the same spectral-gap
   hypothesis and does not say so (see F1). `UnboundedTrialBlock` names an *unbounded ambient*
   with a *bounded* compression; the 2026-08-31 note on S2-tan-theta already recorded that this
   name misled a certificate once.
6. **The unqualified legacy aliases name different clauses.** `SectionTwo.tanTheta_complex` and
   `SectionTwo.tanTwoTheta_complex` are the *ambient* clause; `SectionTwo.sinTwoTheta_complex`
   is the *directed* clause. The module documents this, which is the right stop-gap; the right
   end state is to retire the unqualified names and keep only `_directed_`/`_ambient_`.
7. **Unused parameter.** `Proposition4_2_compact_nonacute` takes `(_J : halmosSourceDefect ≃ₗᵢ halmosTargetDefect)`
   and never uses it; `Proposition4_2_infiniteDimensional` (the strictly stronger theorem) does
   not take it. The compact one is redundant as a registered witness.
8. **Inventory bloat.** S2-sin-two-theta registers 51 declarations and S2-tan-two-theta 66,
   most of them proof structure (`diagonalPart_sq_add_offDiagonalPart_sq`,
   `complexifyReal_addBounded`, …). `canonical_evidence` is what a reviewer needs; the
   `lean_declarations` list should be the canonical witnesses plus explicitly-roled
   correspondence lemmas, not the proof's dependency closure. One canonical entry on
   S2-sin-two-theta (`sinTwoTheta_ambient_bounded_symmetricNorming_complex`) has
   `covers_source_atoms: []`, i.e. it is canonical evidence for nothing.

### F7 — The norm-class model is narrower than "every unitarily invariant norm" (disclosed as "literal"; it is not)

`SymmetricNormingFunction` is the Mirsky/Gohberg--Krein class: a dimension-coherent symmetric
gauge `Φ` on finite sequences, extended to operators by `sup_n Φ(a₀,…,a_{n−1})`. Its docstring
calls this "the literal Davis--Kahan class of unitarily invariant norms". In infinite
dimension it is not: `‖T‖' := ‖T‖ + ‖π(T)‖` (π the Calkin quotient) is unitarily invariant,
normalized on rank one, contraction-monotone, and satisfies Fan dominance (weak majorization
of approximation numbers forces both `a₀` and `lim aₙ` to be ordered), so every Section 2
proof in the paper goes through for it — yet it is not `sup_n Φ(prefix)` for any coherent `Φ`
(on finite rank it agrees with the operator norm, whose extension is the operator norm). This
is a modeling boundary, not a defect in any theorem; but the census should say "the
symmetrically-normed-ideal class" rather than "the literal class", and the row-level note that
`KyFanDominantIdealFamily` versions are "stronger in their own quantifier but not the printed
one" has it backwards for exactly such norms. Low severity.

### F8 — The documented hard gate does not pass on `main`, and one of its options crashes

1. `python3 scripts/certify_davis_kahan_1970.py --require-terminal` (default output directory,
   run at `ba8a72fe`) reports `overall_status: FAIL` with two `failure_reasons`:
   * `DavisKahan.All emitted warnings` — 81 production-build warnings
     (`production_build_warning_count`), and the certificate refuses warnings unless
     `--allow-warnings` is passed. By category: 28 `linter.unusedSectionVars` (the
     `omit … in` debt CLAUDE.md names as cleanup-in-touched-files), 12 unused `simp` arguments,
     5 never-executed tactics, 4 `simpa`→`simp`, 5 deprecated Mathlib names
     (`ContinuousLinearMap.mul_apply`, `coe_comp'`), 2 no-op `rw`s. Heaviest files:
     `DoubleAngle/TangentTransport.lean` (7), `Section9/DomainLimitation.lean` (6),
     `Section3Theorem31Realization.lean` (5), `PartialMap/{UnitaryConjugation,Complexification}.lean` (5 each),
     `Ideals/HilbertSchmidt{RealDescent,ComplexFamily}.lean` (5 each), `Sylvester/Gap.lean` (4).
     So the command CLAUDE.md gives as "the recommended compiler-evidence run" is red on the
     current tree; the 29/29 terminality it computes is correct, but nobody can currently
     produce a green certificate bundle without `--allow-warnings`.
   * `source/config files changed while certification was running` — caused by this review
     writing its report into `dev/` mid-run; not a repository defect, recorded so the FAIL is
     not misread. (The mid-session merge `ba8a72fe` touched only `papers/` and the tooling
     gitlink, not the Lean tree or the ledgers.)
2. `--output-dir <path outside the repository>` passes steps 01--09 and then crashes in
   `main()` at `probe_path.relative_to(ROOT)` (`ValueError: … is not in the subpath of …`).
   The option is advertised and unusable off-tree.

### F9 — Row text that is now wrong or misleading

* DK-6.3-thm `source_clauses.justification` (both fields) describes the spectral-gap
  hypothesis as the established clause (F1).
* S2-tan-theta `review_note`: "The directed conclusion is closed at full source scope" is true
  only because of `tanTheta_directed_unboundedRitz_*`; the note still names the
  `_unboundedTrial_` pair as "registered primaries" for the directed clause in its 2026-08-31
  paragraph, which is the pair F1 is about.
* `source_representation_conventions.crossed-defect-dimension-equality.witness_scope` still
  says the infinite-dimensional reading "is not written, and until it is, … is a representation
  convention rather than a theorem", while the same file's `closed_obligations` records that
  `crossedDefectsEquivalent_iff_sameDimension` closed it the same day. One of the two
  paragraphs is stale; the theorem exists and compiles.
* The `HasDefinedAmbientTangent` block comment says "The (3.5) endpoints above remain as the
  non-vacuous corollary". They are non-vacuous, but by a proof-internal fact the types do not
  state (F3.1).

### F10 — Positive finding: the Proposition 4.4 refutation is correct and independently checked

`shortRotation_fullDisplacement_refuted` lives in `EuclideanSpace ℝ (Fin 4)` (real, as the
printed proposition requires), `U = span(e₀,e₁)`, `W = ½·H` with `H` the stated ±1 matrix,
`V = W(U)`. I checked by hand: `H Hᵀ = 4I` so `W` is orthogonal; `P_U W e₀ = ½(1,1,0,0)` and
`P_U W e₁ = ½(−1,1,0,0)` are orthogonal of norm `√2/2`, so both principal angles are exactly
`π/4 ≤ π/3` and the pair is acute; `W` is a quarter-turn on `span(m₀,m₁)` and the identity on
its complement, so `σ(I − W) = (√2, √2, 0, 0)` and `‖I − W‖₁ = 2√2 ≈ 2.828`; the direct rotation
has `σ(I − U) = 2 sin(π/8)` with multiplicity four, `‖I − U‖₁ = 4√(2−√2) ≈ 3.061`. The printed
Proposition 4.4 is therefore false as stated, the refutation satisfies every printed hypothesis
(`DavisKahanProposition4_4_Finite` quantifies over real finite-dimensional spaces, acute pairs,
`principalAngles U V 0 ≤ π/3`, unitaries carrying `U` onto `V`, and *every*
`UnitarilyInvariantSeminorm`; the witness norm is the trace norm presented as one), and the
repair `directRotation_fullDisplacement_qnorm` (Q-norms) is the natural surviving statement.
The mechanism — spending `2θ` of rotation in one plane and none in the other — is a genuine
mathematical observation the paper missed, and the two-dimensional Example 4.1 (which *does*
turn at `π/3`) is exactly why the printed threshold looked plausible.

## Pass A — selection audit: accepted

* The denominator is the four Section 2 theorems plus the 25 named results of Sections 3--8;
  I re-read the TeX in order and found no named theorem/proposition/lemma/corollary missing and
  nothing included that the paper does not establish. Section 9 and 10 are excluded as they
  should be; `DK-10.4`'s established specializations are handled as fidelity atoms, not
  results.
* Boundary reviews I checked in detail (S2-tan-theta, DK-4.4-prop, DK-6.3-thm, DK-8.1-thm,
  DK-8.2-thm, DK-3.2-prop, DK-3.5-prop, DK-5.1-thm, DK-6.1-prop, DK-6.2-thm) partition their
  blocks correctly. Two `non_result` classifications deserve a sentence: `DK-5.1-thm.roles-interchange`
  and `.one-sided-unbounded-extension` are printed as part of the theorem's statement paragraph
  ("The roles and hypotheses … may be interchanged", "the same proof also covers …"); the
  repository classifies them as post-result consequences *and formalizes them anyway*
  (`banach_sylvester_lower_bound_interchanged*`, `_unboundedA`), so nothing is lost.
  `DK-6.2-thm.rank-corrected-operator-consequence` is a consequence remark, correctly excluded,
  and has no Lean form; that is permitted by the definition of 100%.
* `S2-sharpness` (constants best possible, simultaneous equality) is correctly a non-result
  block; the tree nevertheless has `SharpIdeal.lean`/`SharpKyFan.lean`/`Sharpness.lean`.

## Pass B — result-by-result

Legend: **OK** = registered evidence states the printed result at printed scope (or with
strictly weaker hypotheses); **OK−** = OK with a statement-honesty or registration remark;
**NARROW** = registered canonical evidence is a proper specialization of the printed result.

| result | verdict | notes |
| --- | --- | --- |
| S2-sin-theta | OK | `sinTheta_unbounded_formGap_symmetricNorming_rclike`: unbounded self-adjoint `LinearPMap` ambient, arbitrary dimension (separability not even assumed), `IsTrialResidual` (isometric `E₀`, domain-aware residual), `IsExactSpectralDecomposition` (exhaustive orthogonal isometries with `A F₁ = F₁ Λ₁` on `dom Λ₁` — weaker than "Q reduces A+H"), `FormBoundedSylvesterGap` with the interval/exterior branch symmetric in the two blocks (the printed "or interchanged") and both half-line branches as form bounds (weaker than spectral containment), conclusion on the paper's own `(1 − F₀F₀*)E₀` plus ideal membership. Real and complex fixed-field siblings. Nothing junk-valued. The trial block `A₀` is an arbitrary self-adjoint operator, not required to be a block of an unperturbed `A` — a harmless generalization. |
| S2-tan-theta | OK− | Directed clause at printed scope via `tanTheta_directed_unboundedRitz_*` (unbounded Ritz compression, arbitrary reducing `V` with coercive complement); F3.3 applies to the tangent representative. Ambient clause: `_definedTangent_` endpoints faithfully model the Section 1 vacuity convention with the biconditional to `π/2 ∉ spectrum`; (3.5)-form endpoints are non-vacuous by a proof-internal fact (F3.1). The `residual = Uᗮ H U` hypothesis is exactly "U reduces A − H" given the Rayleigh--Ritz compression, i.e. the printed `H₀ = 0` plus "P reduces A". Noted: no `IsSelfAdjoint A` hypothesis on the unbounded-Ritz endpoints — the theorems are more general than printed, which is fine. |
| S2-sin-two-theta | OK− | Directed clause exact (`V`, `M` arbitrary; gap on any measurable spectral split of `A`; `directedSinTwoAngleOperator V U` in the paper's trial-side order — the 2026-09-04 orientation fix checks out against `‖sin Θ₀‖ = ‖Q^⊥E₀‖`). Ambient clause: F5. Both clauses in one declaration (`sinTwoTheta_bothConclusions_*`) is a good reviewer surface. I checked that `sin 2Θ` needs no (3.5): it vanishes on both crossing subspaces regardless. |
| S2-tan-two-theta | OK− | Directed: `U` reducing `A`, `B` odd for `U` (`H₀ = H₁ = 0`), `V` reducing `A+B`, form bounds `a`/`b` on `U`/`Uᗮ` within `dom A`, conclusion identifies `aₙ(tan 2Θ₀)` as `tan(arcsin aₙ(sin 2Θ₀))` and certifies `aₙ(sin 2Θ₀) < 1` (pole excluded by the type). Ambient: `P = specRange A (Iic c)` is forced by the ordered gap, `ReflectionIntertwines A B V` is built from `ReducesSubspace (A+B) V`; conclusion on `|tan 2Θ|`, correct since a UI norm sees only singular values; F3.2 on pole disclosure. Note `doubleSecant` is a `Ring.inverse`, total; the `aₙ` identity plus `aₙ < 1` make the directed statement self-certifying. |
| DK-3.1-prop | OK | `IsAcute` is Definition 3.2 verbatim; existence, unitary, intertwining, `C₀,C₁ ≥ 0`, `S₁ = S₀*` (as `Uᗮ W U = −(U W Uᗮ)*`), and uniqueness among unitaries with positive diagonal blocks (the printed "already characterizes it"). `RCLike`-generic. |
| DK-3.2-prop | OK | `(∃ T, IsDirectRotation U V T) ↔ CrossedDefectsEquivalent U V` for all pairs (the acute case makes both sides true, so dropping "outside the acute case" is a strengthening); non-uniqueness under `¬IsAcute`. `CrossedDefectsEquivalent` is the constructive reading of (3.5) and `crossedDefectsEquivalent_iff_sameDimension` proves it equal to "equal finrank or both infinite-dimensional" at separable scope — the previously open obligation is genuinely closed. (1.5) is implied by (3.5) via the Halmos decomposition, so its absence from the iff is not a hole. |
| DK-3.3-prop | OK | Forward: direct rotation ⇒ `IsPrincipalUnitarySquareRoot ((2P_V−1)(2P_U−1))` (unitary, square, spectrum in the closed right half-plane). Converse adds the printed image condition `T '' (U ∩ Vᗮ) = Uᗮ ∩ V`. Real versions present. |
| DK-3.4-prop | OK | `‖x‖²/2 ≤ ‖P_V x‖²` on `U` is `C₀² ≥ ½`; `W·W` is a direct rotation from `reflectedSubspace U V` (= `Q₋𝓗`) to `V`, all five defining clauses concluded. |
| DK-3.1-thm | OK | Forward: unitary equivalence of pairs ↔ equality of the four Halmos summand dimensions (as isometric equivalences) ∧ `SameSpectralMultiplicity` of the generic cosine blocks, at `[SeparableSpace]`. `SameSpectralMultiplicity` is a genuine Hahn--Hellinger datum (measure class + antitone level sets), not unitary equivalence in disguise. The invariant is a faithful re-expression of "(mult Θ₀, mult Θ₁)": point masses at `0`, `π/2` are the four trivial summands and the generic parts are intertwined. Converse: takes only `Θ₀, Θ₁` self-adjoint with spectrum in `[0, π/2]` and `SameSpectralMultiplicityAwayFromZero` (multiplicity data of the restrictions to `(ker sin Θⱼ)ᗮ`), constructs `J₀`, and identifies the four Halmos pieces of the realized pair with the kernels of `sin Θⱼ`, `cos Θⱼ`; combined with `theorem3_1_realization` this gives `cos² Θⱼ` as the compressions. The 2026-09-04 closure is real. |
| DK-3.1-cor | OK | Compactness of `P_U(1−P_V)P_U` (= `PQ^⊥P`), invariants reduce to `compactAngleEigenvalueList` (approximation numbers of the positive compact block, i.e. eigenvalues with multiplicity); realization of any antitone `θ → 0` in `[0, π/2]`; zero-multiplicity freedom. The `prescribedAngleSequence` version needs `0 < θₙ < π/2` and is a specialization — correctly not canonical. |
| DK-3.5-prop | OK | Commutation with `P, Q, J, U`; `Θx = θx ⇒ ∠(x, Ux) = θ`; acute-case unique maximal reducing subspace with `IsPrintedFixedCosineReducingSubspace` indexed by `{M ∩ U, M ∩ Uᗮ}` as printed. `U = e^{JΘ}` and `cos²Θ = PQP + P^⊥Q^⊥P^⊥` are correctly pre-result setup atoms. |
| DK-3.2-cor | OK | `Θ(V,U) = Θ(U,V)`, `J ↦ −J`, `U ↦ U*` under the swapped defect identification. |
| DK-4.1-prop | OK | Compact/matched-defect setup is printed inside the 4.1 block, so `locally_exact` is defensible. Orthonormal family indexed by the indices with `sin θₙ > 0` (the only reading that is not false when `PH` is finite-dimensional and the sequence is zero-padded), `aₙ((1−U)P) = 2 sin(θₙ/2)`, and `aₙ((1−U)P) ≤ aₙ((1−W)P)`. |
| DK-4.1-cor | OK | UI-norm minimality of `(1−V)P` over unitaries carrying `U` to `V`, at `SymmetricNormingFunction` and at `KyFanDominantIdealFamily`, with and without compactness. Nonlocal reading (Section 4 setup) accepted. |
| DK-4.2-prop | OK | `∑' sin²θₙ ≤ ∑' sin²∠(vᵢ, Wvᵢ)` in `ENNReal` for every `HilbertBasis` of `U` — handles the infinite right-hand side as printed; version without compactness present. F6.7. |
| DK-4.3-prop | OK | `N((1−U*)(1−U)) ≤ N((1−W*)(1−W))` with membership, both norm vocabularies. |
| DK-4.4-prop | OK | F10. Refutation and Q-norm repair both compile on standard axioms. |
| DK-5.1-thm | OK | Banach `X, Y`, `‖B‖ ≤ γ`, explicit two-sided inverse with `‖A⁻¹‖ ≤ (γ+δ)⁻¹`, `CompatibleCrossOperatorNorm` (norm, both-sided contraction compatibility), `δ N(T) ≤ N(C)`; the `_uiNorm` form needs only a left inverse and subadditivity; interchanged and unbounded-`A` remarks formalized. |
| DK-5.2-thm | OK | `A ≥ c+δ`, `B ≤ c` as form bounds on self-adjoint `LinearPMap`s, `SylvesterEquation` = `X(dom B) ⊆ dom A ∧ A X x − X B x = C x`, membership concluded; real and complex; both norm vocabularies. |
| DK-5.1-lem | OK− | Mathematics present at `ℝ` and `ℂ`; registration is a typeclass wrapper (F4). |
| DK-6.1-lem | OK | Hypotheses in Ky Fan form (weaker than "every UI norm"), conclusion in `extendedGauge` (no membership needed); converse under `SameApproximationSingularValues` (equisingular) with Ky Fan conclusion — the printed "every UI norm" conclusion follows by the repository's own Fan-dominance adapter, but the converse could state it directly. |
| DK-6.2-lem | OK | `N(diagonalPair U V K) ≤ N(K)` with membership. |
| DK-6.1-prop | OK | Bounded symmetric `A, B` with `U`, `V` reducing, two `FormBoundedSylvesterGap`s (the printed two-sided separation), conclusion on `sinAngleOperatorC U V` = `|P_U − P_V|`; unbounded common-domain forms registered. |
| DK-6.1-thm | OK | Non-isometric `E₀` with `LowerFrameBound E₀ ε`, `IsTrialResidualEquation` (no isometry), exhaustive `F₀, F₁`, any `SinThetaRepresentativeAcross` of `PQ^⊥` (the printed "any operator with the same singular values"), `δ ε N(S) ≤ N(R)`, unbounded `LinearPMap`s. |
| DK-6.2-thm | OK | Same data with `PairwiseSpectrumGap`, Hilbert--Schmidt norm, finiteness of `approximationNumberEnergy` concluded. |
| DK-6.3-thm | NARROW | F1. |
| DK-6.3-lem | OK | `K P = Q K P`, `rank P, rank Q ≤ n`, energy defect `< η²` ⇒ `‖Q K (1 − P)‖ < η`; approximation-number form in arbitrary dimension and singular-value form in finite dimension. (The Lean conclusion is strict `<`; the printed is `≤`; strict is stronger.) |
| DK-8.1-thm | NARROW (scope) | Content complete at bounded scope: existence of the canonical low branch with `Theorem81Conclusion` (which also *concludes* spectral repulsion `spec(A+H) ∩ (α, α+δ) = ∅` — a nice extra), the quarter-angle iff for every reducing `M`, (i) as form inequalities, (ii) as approximation-number inequalities with `‖C₁‖²`, (iii) for every `FiniteSymmetricGauge`. F2. |
| DK-8.2-thm | NARROW (scope) | Content complete at bounded scope: both smallness alternatives, `spec(A₀) ⊂ [β−δ/2, α+δ/2]`, retained sin 2θ bounds on the trial-side directed angle (orientation fixed 2026-09-04, checked), and ambient `maximalAngle P Q < π/4` under (3.5) in constructive form; the directed `directedGap < √2/2` supporting form needs no (3.5). F2. |

## Pass C — nonlocal source interpretations

| row | verdict | driver |
| --- | --- | --- |
| S2-tan-theta | **PASS paper-faithful nonlocal interpretation**, with F3.1 reservation | The `_definedTangent_` endpoints model the Section 1 vacuity convention and nothing later; `hasDefinedAmbientTangent_iff_pi_div_two_notMem_spectrum` makes the hypothesis exactly "the printed norm exists". The (3.5)-form endpoints read the Section 3 standing convention back into a Section 2 theorem, which the row correctly no longer relies on. I verified independently that the ordered gap with `H₀ = 0` forces `P ∩ Q^⊥ = 0`, so under (3.5) both crossing subspaces vanish and the two readings coincide in content. |
| DK-4.1-cor, DK-4.2-prop, DK-4.3-prop | **PASS** | The compact/matched-defect setup is fixed at the head of Section 4 inside the 4.1 block and the section declares itself independent of later material; the Lean witnesses take `IsCompactOperator (principalSineOperator U V)` and the constructive (3.5) datum `J`. The infinite-dimensional (no-compactness) versions of 4.1-cor and 4.2 exceed the printed scope. |
| DK-8.2-thm | **PASS** on (3.5); **see F2** on operator scope | The printed `Θ < π/4` is ambient; without (3.5) a vector in `P^⊥ ∩ Q` contributes `π/2` and the statement is false, so the standing convention is load-bearing, correctly linked as `S3-standing-scope.crossed-dimension-standing-assumption`, and now backed by a theorem rather than a convention. |

## What this review did not do

* It did not re-derive the paper from the original PDF; the checked-in TeX was taken as the
  source of record, per the audit prompt.
* It did not read proofs, except where a type could be junk-valued (F3), in which case it
  read enough of the proof to determine whether the junk case is excluded internally.
* It did not audit Section 9, Section 10, the `Challenge/` conformance surface, the
  comparator configs, or any of the other four papers in the workspace.
* It did not attempt to evaluate whether the `SameSpectralMultiplicity` spectral-representation
  machinery in `ForTauCeti/…/BorelCalculus/` is correct beyond the fact that it compiles on
  standard axioms; that is a Tau Ceti review question.

## Recommended order of repairs

1. **F1** — re-register DK-6.3-thm's canonical evidence onto
   `tanTheta_directed_unboundedRitz_symmetricNorming_{complex,real}`; fix the two
   justification strings; rename the `_unboundedTrial_` pair with `spectralGap`. Census-only.
2. **F2** — decide Section 8's operator scope and write it down on both rows (or lift).
3. **F4** — register the `ℝ`/`ℂ` strong-cutoff proofs as DK-5.1-lem's witnesses.
4. **F5** — promote `sinTwoTheta_ambient_unbounded_reflectionPair_symmetricNorming_rclike`
   (or fixed-field aliases of it) to canonical evidence for the ambient sin 2θ clause and point
   `SectionTwo.sinTwoTheta_ambient_*` at it.
5. **F3** — add the pole/definedness conjuncts to the tangent endpoints' conclusions (they are
   already proved inside each proof).
6. **F6.1, F6.2** — move `SineTheta/Presentation.lean` under `TauCeti`, deregister the
   case-twins. Then F6.3--F6.8 and F9 as a single census-hygiene commit.
7. **F8** — clear the 81 production warnings (mostly `omit … in` lines and dead `simp`
   arguments) so the documented certificate command is green; fix `--output-dir`.
8. **F7** — wording.

---

## Closure, 2026-09-05

Written by the repair pass, not by the reviewer. The findings above are left as they
were written. This section says, for each one, what closes it and where — and says
plainly which ones are not closed.

A second, independent hostile review arrived between the report above and this repair
pass. It accepted the four commits that answered its own previous round, agreed with
F1, F4 and F5, and reopened three things the report above under-rated: the norm class
(F7, which the report treated as wording), the directed tangent representation, and the
separability policy. It also raised Theorem 3.1's ambient-dimension clause, which the
report above did not reach. Those four are treated as first-order below, ahead of the
report's own ordering, because that is what the follow-up review asked for.

### Closed

**Norm class (F7, promoted to a semantic finding).** Closed by a theorem, not by
wording. `TauCeti.DavisKahan1970.kyFanDominant_of_symmetricNorming`
(`SymmetricNormingFanDominance.lean`, commit `23fc0954`) transports any estimate proved
over every `SymmetricNormingFunction` to every `KyFanDominantIdealFamily`, by
instantiating at `kyFanNormingFunction k` — the Ky Fan gauge presented as a coherent
symmetric norming function, which was already in the tree in
`Ideals/KyFanNorm.lean` and which the report and the follow-up review both missed.
`symmetricNorming_iff_kyFanDominant` states the resulting equivalence with the existing
forward bridge. So the two quantifiers are the same assertion — each is weak Ky Fan
majorization, which is the criterion Section 1 of the paper announces at (1.11)–(1.13)
— and a `SymmetricNormingFunction` endpoint does deliver the printed "every
unitary-invariant norm", including at norms outside the symmetrically normed ideals such
as the Calkin-augmented `‖T‖ + ‖π(T)‖` the follow-up review named. The four Section 2
rows carry the reading in a new `norm_class_reading` field and register the transports;
the two unitary-invariant-norm atoms' `type_requirements.rationale` says why the token
they check for is not a narrowing. No endpoint was restated and no row's norm quantifier
moved, because none needed to.

**Directed `tan Θ` representation.** Closed by re-registration, commit `23fc0954`.
`S2-tan-theta`'s directed clauses and `DK-6.3-thm` now canonicalize
`tanTheta_directed_unboundedRitz_symmetricNorming_exists_{complex,real}`, which take
only the source data — an unbounded Ritz pair, an arbitrary reducing complement, the two
ordered form bounds, and the paper's residual `R` of (1.8), now an explicit bounded
operator in the type — and *derive* the pole exclusion and *construct* the tangent
representative. The parameterized `_unboundedRitz_` pair the follow-up review objected to
is `alternative_route`. This also closes F3.3 at the canonical surface: the `_exists_`
conclusion carries `∀ n, aₙ(theorem63DirectedSineBlock Z V) < 1`.

**F1 — DK-6.3-thm's spectral-gap hypothesis.** Same commit. The `_unboundedTrial_` pair
is `specialization`, with the extra hypothesis named in its note and in the row's
`review_note`; the 4×4 instance from the report is cited there.

**F4 — Lemma 5.1's capability class.** Commit `dd33d00d`. `lemma5_1_complex` and
`lemma5_1_real` state the lemma at the paper's two fields with nothing in the signature
but the paper's hypotheses; `Lemma5_1` stays a `scalar_generic_facade`.

**F5 — the ambient sin 2θ clause.** Commit `13cff6da`.
`sinTwoTheta_ambient_unbounded_reducing_symmetricNorming_{rclike,complex,real}` take
`ReducesSubspace A U` and `ReducesSubspace (A + H) V` — the printed hypothesis, no
spectral subspaces. The bridge is `ReflectionIntertwines.ofReducesSubspace` plus the new
scalar-generic `addBounded_reflectionPerturbation_intertwines_of_commutes`, the `RCLike`
core of the existing ℂ-and-spectral `add_reflectionPerturbation_intertwines`.
`SectionTwo.sinTwoTheta_ambient_*` and the ambient conjunct of
`sinTwoTheta_bothConclusions_*` were retargeted, so the both-conclusions certificate now
quantifies over a reducing subspace rather than a measurable set. The canonical entry
with an empty `covers_source_atoms` is demoted to `specialization`.

**Separability.** Commit `4c968186`. Measured rather than argued: 28 of the 29 rows have
canonical evidence assuming no separability at all, and `DK-3.1-thm` is the one row where
it appears. `ambient_scope_policy` states the rule — a source-wide ambient convention is
not a per-result hypothesis, so omitting it is an accepted generalization and carrying it
is the printed scope exactly — and `_validate_ambient_scope_policy` *derives* each row's
posture from the compiler-printed types and fails when the table disagrees, or when a
witness assumes separability with no entry saying why. Checked against a deliberate flip.
The stale docstring the follow-up review caught, on the real Theorem 3.1 converse, is
corrected: `A₀` never carried separability and the signature never did.

**Theorem 3.1's ambient-dimension clause.** Commit `ad3cc210`.
`theorem3_1_realization_inAmbient_ofSpectralMultiplicityAwayFromZero_{complex,real}` take
the printed clause as `e : WithLp 2 (A₀ × A₁) ≃ₗᵢ[𝕜] H` and exhibit the realized pair
inside `H` as the isometric image of the model pair, with
`PairOfSubspacesUnitaryEquivalent` between them in the conclusion. They are the canonical
evidence; the ambient-free realizations are `generalization`. The reading of `e` as "their
domain dimensions sum to `dim H`" is registered as the representation convention
`theorem31-ambient-dimension`, with `nonempty_linearIsometryEquiv_of_hilbertBasis` as its
compiled witness.

**F2 — Section 8's operator scope.** Commit `76c8e360`, and *not* by the metadata-only
route the report offered as Option A, which the follow-up review refused. Both rows now
carry an argued reading with its source evidence: Section 1 fixes bounded as the setting
and unbounded as an allowance; the Section 2 scope paragraph attaches that allowance to
*the four main results* and locates the extra analytic work in Theorem 5.2 and the
Appendix to Section 6, naming no Section 8 counterpart; and Section 8 restricts its own
parts (ii) and (iii) to finite dimensions, so a section that says nothing about unbounded
operators is being read rather than silently narrowed. The competing reading is stated in
full, including that (8.1)/(8.2) survive an unbounded `A`. `DK-8.1-thm` moves from
`locally_exact` to `paper_faithful_nonlocal_source_interpretation`. **The lift is the
honest end state and remains open**, tracked as `DK-S8-UNBOUNDED` in `GOAL.md`.

**F3 — junk-valued functional calculus in conclusions.** Closed in two commits. The directed
clause's canonical witnesses derive their pole exclusion and conclude it. The eight ambient
`tan Θ` endpoints stated under condition (3.5) now conclude `HasDefinedAmbientTangent U V`
(`HasDefinedAmbientTangentReal` over `ℝ`; the two bounded ones, whose files sit below the
definition, conclude the equivalent `‖sin Θ‖ < 1`). Both ambient `tan 2Θ` endpoints now
conclude `∀ t ∈ spectrum ℝ (angleOperator…), Real.cos (2 * t) ≠ 0`.

Every conjunct was already proved inside the corresponding proof. The unbounded-Ritz tangent
case needed no new lemma — `norm_sinAngleOperatorC_lt_one_of_unboundedRitz` and
`norm_sinAngleOperatorR_lt_one_of_unboundedCompression_crossedDefectsEquivalent` were already
in the tree. The real `tan 2Θ` case needed one:
`cos_two_ne_zero_of_isUnit_diagonalPart_reflection_sq_real`, because the real chain carries
the `IsUnit` form of the fact while the existing exclusion lemma is stated for
`angleOperatorC`; it is proved by complexification through `spectrum_complexify`.

The `HasDefinedAmbientTangent` block comment, which called the (3.5) endpoints a non-vacuous
corollary, now records that they state it.

**F6 — naming and placement.** Seven of the eight sub-items are done.

* F6.1 `SineTheta/Presentation.lean` declares into `TauCeti.DavisKahan1970`, so its
  seventeen registered declarations, including the canonical `sin Θ` witness and the
  `IsTrialResidual` / `IsExactSpectralDecomposition` predicates, are no longer in the root
  namespace.
* F6.2 the six case-twin pairs are gone: the capitalized member of each was an alias for a
  *record method*, a different theorem from the lowercase canonical one. No two registered
  names now differ only in case.
* F6.3 sixty-one source-facing declarations moved to the lowercase `theoremN_M_*` form.
  Structures and namespaces keep their CamelCase.
* F6.4 the six registered witnesses outside the paper namespace are reachable under it:
  `Section2TanThetaPerturbation.lean` declares into `TauCeti.DavisKahan1970`, and the
  Theorem 6.3 ideal-gauge pair, the real Sylvester generalization and the three
  Proposition 4.4 declarations gained source-facing aliases.
* F6.5 `UnboundedTrialBlock` is `BoundedCompressionTrialBlock`; its compression is bounded,
  and the old name had already misled one certificate.
* F6.6 the six unqualified clause aliases are `@[deprecated]`, pointing at the
  `_directed_`/`_ambient_` name that says which conclusion they are. The `SectionTwo.lean`
  module docstring went from 246 lines to 74.
* F6.8 eleven proof-structure entries are deregistered from the two double-angle rows, and
  the fifteen remaining un-noted `supporting_theorem` entries gained a role and a sentence.

**F6.7 is declined, with the reason recorded on `DK-4.2-prop`.** The review asked for
`proposition4_2_compact_nonacute` to be deleted because its `_J` binder is unused. It is
unused deliberately: Section 4 fixes the compact/matched-defect setup inside the
Proposition 4.1 block and prints 4.2 under it, `AGENTS.md` says a source-facing statement
retains the paper's hypotheses even where the proof does not consume them, and the
unconditional theorem is already registered as a `generalization`. Deleting it would make the
canonical witness stop carrying the setup this row's own accepted nonlocal reading says it is
printed under.

**F8 — the 81 production warnings.** Commits `551ebe1a`, `3fe37b1f`, `60c442f2`,
`1b6ca96c` (merged as `70c367e6`) and `33e257f9`. `lake build DavisKahan.All` is
warning-free, so `certify_davis_kahan_1970.py --require-terminal` runs without
`--allow-warnings`. The count was 72 warnings, not 81; the report's figure counted nine
`Hint:` continuation lines ending in the word "warning:".

**F9 — stale row text.** Commit `2f75ba2c` for the norm-class notes and the
`crossed-defect-dimension-equality` `witness_scope`, which still called the
infinite-dimensional reading of (3.5) unwritten after
`crossedDefectsEquivalent_iff_sameDimension` closed it. Commit `23fc0954` for the
`S2-tan-theta` review note that named the `_unboundedTrial_` pair as the directed
clause's registered primaries.

**F10.** A positive finding; nothing to close.

**F7's `--output-dir` bug.** Fixed. `certify_davis_kahan_1970.py` called
`relative_to(ROOT)` on five paths that the option can move outside the tree, and crashed on
the first of them after nine successful steps. A `path_arg` helper now returns a repository-
relative path when the target is inside the tree and an absolute one otherwise, which is what
every spawned command needs, since they all run with the repository as their working
directory. Verified: `--require-terminal --output-dir <path outside the repository>` now
reports `status: PASS`, 29/29.

### Not closed

Nothing from this report. Three things remain open and are tracked in `GOAL.md`, none of them
a finding of this review: the Section 8 unbounded lift (`DK-S8-UNBOUNDED`), which would make
the operator-scope reading recorded under F2 moot; the comparator signature check, red on
eight of twenty Davis--Kahan comparisons since before this pass and untouched by it; and the
`per-declaration-expose` ratchet and the two Tau Ceti readiness gates, which the repository
already tracked as known non-blocking debt.
