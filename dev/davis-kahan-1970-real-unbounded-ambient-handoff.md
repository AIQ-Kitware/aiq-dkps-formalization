# Handoff: the real unbounded ambient `tan Θ` endpoint (closes `S2-tan-theta`)

> **DISCHARGED 2026-08-13.** `tanTheta_unbounded_ambient_paperUINorm_real_exact` is proved in
> `DavisKahan/Sources/DavisKahan1970/TanThetaUnboundedAmbientReal.lean`, with the required
> signature and standard axioms, and `S2-tan-theta` is accepted terminal — the denominator is
> 29/29. This document is retained as the record of the plan and of what the execution
> actually needed. Two deviations from the plan below are worth carrying forward:
>
> - **Step 6 was not needed.** Rather than rebuilding the complex lower-corner Ky Fan
>   estimate, the complex `tanTheta_unbounded_ambient_paperUINorm_of_data` was split into
>   `..._of_data_of_transversality` (the assembly half, taking `‖sin Θ‖ < 1` directly) plus
>   the unchanged original, which now derives transversality from (3.5) and calls it. The
>   real endpoint consumes the assembly half. No corner argument is duplicated.
> - **Step 5 was one `ext`.** The residual-block transport is
>   `complexifyTrialData_residual_eq_projectionBlock`, proved from
>   `starProjection_complexifySubmodule_orthogonal` and
>   `coe_complexifySubmoduleEquiv_eq_complexify_subtypeL`; no hypothesis was added.
>
> Everything else — the architecture, the API inventory, the stop conditions, the accounting
> steps — held as written.

**Written 2026-08-12, immediately after the `S2-tan-theta` nonlocal-source-semantics work.**
Everything described below is verified against the checkout at commit `5bfa2624`; every
declaration named here was resolved in the tree, not recalled.

## The one blocker

`S2-tan-theta` is the last nonterminal row of the 29-result denominator, and it is
nonterminal for exactly one mathematical reason:

> the unbounded ambient `tan Θ` factor-one theorem exists at arbitrary
> `PaperUnitaryInvariantNorm` scope over `ℂ`, but no source-facing `ℝ` counterpart is
> registered.

Close that, re-audit the row, re-close it. Nothing else about the row is open.

### What is already closed, and must not be reopened

The source-interpretation question is **settled and accepted**. The printed Section 2
ambient conclusion does not state the crossed-defect condition (3.5); the source
introduces (3.5) in Section 3, assumes it as standing thereafter, and proves this theorem
in Section 6 inside that scope, having already announced in Section 1 that results are
vacuous when a displayed norm fails to exist. The row is classified
`paper_faithful_nonlocal_source_interpretation`.

Do not reopen that analysis. Do not classify the theorem as refuted. Do not rewrite the
Section 2 statement to contain (3.5). Do not remove or weaken any of:

- the §1 norm-existence/vacuity convention atom;
- the Section 3 standing (3.5) atom;
- the finite-dimensional automatic case;
- the bilateral-shift right-angle vacuity witness;
- the Section 6 proof-context dependency;
- the hostile-review warning or the competing literal reading.

`CrossedDefectsEquivalent U V` in the new theorem is **expected and correct**. It is the
audited explicitation of (3.5). Do not drop it to make the Section 2 display look cleaner.

## Required endpoint

```lean
theorem tanTheta_unbounded_ambient_paperUINorm_real_exact
    (N : PaperUnitaryInvariantNorm)
    (A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := E))
    {U V : Submodule ℝ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (D : UnboundedTrialBlock A U)
    (H : E →L[ℝ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : E)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A.toLinearMap x) =
        A.toLinearMap ⟨Vᗮ.starProjection ((x : E)), hVdom x⟩)
    (hCompression : ∀ z : U, ⟪D.operator z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪A.toLinearMap ⟨y, hy⟩, y⟫_ℝ)
    (h35 : DavisKahan.Frontier.CrossedDefectsEquivalent U V)
    (hResidual : D.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    N.Mem (paperTanAngleOperatorR U V) ∧
      delta * N.gauge (paperTanAngleOperatorR U V) ≤ N.gauge H
```

Note `DKClosedOperator` is a **ℂ-only** abbreviation
(`DavisKahan/SpectralTheory/ClosedOperator/MathlibBridge.lean:27`); spell the real carrier
as `TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℝ)`. `UnboundedTrialBlock`
(`DavisKahan/TanTheta/UnboundedSpectrum.lean:44`) is already scalar-generic and its own
docstring says so.

**Hostile signature check before promoting.** Reject the theorem if its elaborated type
gained any of: `FiniteDimensional`, compactness, a caller-supplied
`‖paperSinAngleOperatorR U V‖ < 1`, acuteness, a stronger spectral gap, a complexified
residual or perturbation, an operator-norm-only specialization, a scalar-fixed
`KyFanDominantIdealFamily` in place of `PaperUnitaryInvariantNorm`, a domain hypothesis
absent from the real unbounded directed setup, or a factor above one.

## Architecture: do not complexify the unbounded operator

`DavisKahan/Sources/DavisKahan1970/DirectedUnboundedReal.lean` already established the
right route for the directed case, and its module docstring states it explicitly: the
unbounded chain touches its ambient operator only through `Theorem63TrialData` — bounded
data — plus the two printed form bounds. That bundle, `UnboundedTrialBlock`,
`Theorem63TrialData.ofUnbounded`, and `crossed_lower_of_reducing` are all scalar-generic.
Exactly one link is ℂ-only: `all_kyFan_core_of_formBounds_infinite`, whose finite-projector
selection rests on a projection-valued measure that exists only over `ℂ` in the pinned
dependencies. That single link is transported at the **finite Ky Fan level**, where
approximation numbers survive complexification on the nose, so no scalar-fixed ideal family
is ever compared across fields.

Follow the same route:

```text
real unbounded A
  → real Theorem63TrialData
  → real transversality from real directed no-pole data + (3.5)
  → complexify ONLY the bounded trial data and bounded H
  → reuse the existing complex bounded ambient assembly
  → descend paperTanAngleOperatorR and the PaperUI gauge to ℝ
```

Do not build a second theory of complexifying unbounded closed operators.

## Verified API inventory

Every entry below was resolved in the tree at `5bfa2624`.

### Mirror targets (the complex originals to copy)

| Declaration | Location |
|---|---|
| `tanTheta_unbounded_ambient_paperUINorm_exact` | `Sources/DavisKahan1970/TanThetaUnboundedAmbient.lean:268` |
| `tanTheta_unbounded_ambient_paperUINorm_of_data` | `Sources/DavisKahan1970/TanThetaUnboundedAmbient.lean:194` |
| `tanTheta_ambient_paperUINorm_of_lowerCorner` | `Sources/DavisKahan1970/TanThetaUnboundedAmbient.lean:166` |
| `kyFan_lowerCorner_le` | `Sources/DavisKahan1970/TanThetaWholeSpace.lean:1047` |

### Real-side inputs

| Declaration | Location |
|---|---|
| `norm_paperSinAngleOperatorR_lt_one_of_crossedDefectsEquivalent` | `Sources/DavisKahan1970/DirectedReal.lean:659` |
| `approximationSingularValue_sineBlockReal_lt_one_infiniteData` | `Sources/DavisKahan1970/DirectedUnboundedReal.lean:269` |
| `theorem63DirectedSineBlockReal` | `Sources/DavisKahan1970/DirectedReal.lean:54` |
| `paperTanAngleOperatorR` | `Geometry/Angle/PaperOperatorAngleReal.lean:127` |
| `crossed_lower_of_reducing` | `TanTheta/Theorem63UnboundedCompression.lean:178` |
| `Theorem63TrialData.ofUnbounded` (real use sites) | `Sources/DavisKahan1970/DirectedUnboundedReal.lean:385,410` |

### Complexification transports (do not reprove these)

| Declaration | Location |
|---|---|
| `complexifyTrialData` | `Sources/DavisKahan1970/DirectedUnboundedReal.lean:85` |
| `complexifyTrialData_compression_upper` | `Sources/DavisKahan1970/DirectedUnboundedReal.lean:187` |
| `complexifyTrialData_crossed_lower` | `Sources/DavisKahan1970/DirectedUnboundedReal.lean:207` |
| `complexifyTrialData_residual_apply` | `Sources/DavisKahan1970/DirectedUnboundedReal.lean:138` |
| `complexify_paperSinAngleOperatorR` | `Geometry/Angle/PaperOperatorAngleReal.lean:140` |
| `complexify_paperTanAngleOperatorR` | `Geometry/Angle/PaperOperatorAngleReal.lean:164` |
| `coe_complexifySubmoduleEquiv_eq_complexify_subtypeL` | `SpectralTheory/Complexification/SubmoduleEquiv.lean:126` |
| `starProjection_complexifySubmodule_orthogonal` | `SpectralTheory/Complexification/Subspace.lean:232` |
| `PaperUnitaryInvariantNorm.mem_complexify_iff` | `Sources/DavisKahan1970/SineTheta/Norms/ComplexificationGauge.lean:80` |
| `PaperUnitaryInvariantNorm.gauge_complexify` | `Sources/DavisKahan1970/SineTheta/Norms/ComplexificationGauge.lean:89` |
| `all_kyFan_core_of_formBounds_infinite` (the one ℂ-only link) | `TanTheta/Theorem63UnboundedInfiniteTrial.lean:364` |

## Proof steps

1. **Real data-level theorem, kept public.** Prove
   `tanTheta_unbounded_ambient_paperUINorm_real_of_data`, taking
   `data : Theorem63TrialData U V`, real form bounds, `h35`, the residual identity, and
   `N.Mem H`, concluding on `paperTanAngleOperatorR U V`. It is the real counterpart of the
   complex `..._of_data` and makes the final wrapper trivial.
2. **Real transversality, derived natively.** A private helper
   `norm_paperSinAngleOperatorR_lt_one_of_data_crossedDefects` following the proof shape of
   `norm_paperSinAngleOperatorR_lt_one_of_crossedDefectsEquivalent`, but taking its
   no-pole input from `approximationSingularValue_sineBlockReal_lt_one_infiniteData`
   instead of the bounded no-pole theorem. The mathematics is: real directed no-pole plus
   (3.5) gives real ambient `‖sin Θ‖ < 1`. Never take `htr` from the caller.
3. **Complexify the transversality**, via `complexify_paperSinAngleOperatorR` and
   `norm_complexify`. This is why no separate transport of `CrossedDefectsEquivalent`
   through complexification is needed: (3.5) is consumed entirely on the real side, and the
   complex assembly receives only its consequence.
4. **Complexify the bounded data and form bounds** with `complexifyTrialData` and the two
   transport lemmas above.
5. **Transport the residual-block identity** to
   `dataC.residual = (complexifySubmodule U)ᗮ.starProjection ∘L complexify H ∘L (complexifySubmodule U).subtypeL`
   by extensional transport. Do not add a hypothesis to make this easier.
6. **Rebuild the complex lower-corner Ky Fan estimate** essentially verbatim from the
   complex `..._of_data` proof, using `kyFan_lowerCorner_le` and
   `all_kyFan_core_of_formBounds_infinite`. If a new double-corner lemma seems necessary,
   stop — that means the work has dropped below the intended abstraction.
7. **Apply `tanTheta_ambient_paperUINorm_of_lowerCorner`** over `RealComplexification E`.
8. **Descend** with `complexify_paperTanAngleOperatorR`, `mem_complexify_iff`, and
   `gauge_complexify`. The final statement must be about `paperTanAngleOperatorR U V` and
   `H : E →L[ℝ] E`, never left on `RealComplexification E`.
9. **Wrapper**: mirror the complex exact theorem, with
   `Theorem63TrialData.ofUnbounded D V` and `crossed_lower_of_reducing (𝕜 := ℝ)`.

### Stop and report, rather than weakening, only if

1. `complexifyTrialData` cannot preserve the bounded data the complex assembly consumes;
2. real data-level no-pole does not give ambient transversality under (3.5);
3. the real residual block cannot reach the complexified projection block with its
   approximation-singular data intact;
4. `paperTanAngleOperatorR` does not descend exactly from the complex ambient tangent;
5. PaperUI membership or gauge is not preserved by real complexification;
6. the real unbounded hypotheses cannot produce the same `Theorem63TrialData` form bounds.

Report the theorem applied, its elaborated type, the goal, and the mismatch. Do not add a
stronger hypothesis. Ordinary elaboration friction — coercions, `RealComplexification`
adapters, dependent subspace rewriting, subtype-adjoint simplification, scalar casts,
namespace resolution — is not a stop condition.

## Accounting after the proof compiles

1. Add the new declaration to `S2-tan-theta` in
   `dev/davis-kahan-1970-formalization-result-inventory.json` and to the census row in
   `dev/davis-kahan-1970-full-source-census.json`; add a `#check` to
   `DavisKahan/Sources/DavisKahan1970/Audits/ResultSemanticSurface.lean` (the result
   checker rejects any selected declaration missing from that surface).
2. Delete the `remaining_gap` block (`missing_real_scalar_unbounded_ambient_endpoint`) and
   set `disposition` and `semantic_certification` to their terminal values. Update the
   census row's `completion_holes`, `blocked_by`, and `next_action`, and the statement-map
   row's `known_completion_holes` and `audit_warning` — the map checker requires these to
   equal the census values.
3. Update `semantic_review_sweep.terminal_results` to 29 and empty `remaining_results`.
4. **Refresh every hash.** `/tmp` scratch scripts are gone; the recipe is: rehash each TeX
   claim block into the statement map, then the selection review's TeX and atom hashes,
   then the `nonlocal_source_interpretation` block's three hashes (TeX, atom inventory,
   supporting-atom digest). The digest is a SHA-256 over the sorted JSON of
   `{id, summary, reason_code, role}` for each supporting atom, in `supporting_atom_ids`
   order. Editing only the result inventory does not disturb any of them; editing the TeX
   or the atom inventory disturbs all of them.
5. Regenerate the derived views: the audit packet
   (`python3 scripts/render_davis_kahan_1970_audit_packet.py`), the census markdown
   (`scripts/render_davis_kahan_1970_source_census.py`), and by hand the two inventory
   markdown files. **The audit packet embeds declaration source locations**, so it goes
   stale whenever a declaration moves module — that is what made the map gate fail during
   the comparator repair.
6. Update `dev/davis-kahan-1970-result-semantic-review-2026-08-12.md` (the `S2-tan-theta`
   section and the "Remaining mathematical targets" list),
   `dev/davis-kahan-1970-closure-audit-2026-08-12.md`, and
   `dev/davis-kahan-1970-completion-handoff.md`.
7. Do not change the denominator. Do not add a 30th result for any interpretation-support
   atom.

## Gates

```bash
lake build DavisKahan.All                                  # production build
python3 scripts/check_davis_kahan_1970_statement_map.py     # runs the result checker
python3 scripts/check_davis_kahan_1970_source_census.py     # resolves declarations via lake
python3 scripts/check_declaration_name_drift.py             # ~1s, run after any rename
```

Verify by exit code, not by reading piped output.

The result checker fails closed on the interpretation machinery: back-links in both
directions, declaration existence, the three staleness hashes, substantive accepted and
competing readings, and `#check`ed explicitation declarations. Four negative tests were run
against it on 2026-08-12 and all four failed closed. **Changing the selected Lean
declarations does not by itself make the interpretation review stale — but do not assume
it; if the checker says stale, re-review deliberately rather than pasting a new hash.**

`29/29 terminal` is reportable only when every checker accepts the row.

## Known pre-existing failures — not caused by this task

- `python3 scripts/check_dependency_layers.py` fails on backwards imports from
  `DavisKahan.SpectralTheory.FormMethod.Beam*` into Section 9 source facades.
- `python3 scripts/check_comparator_signatures.py --no-build comparator/davis-kahan-1970.json`
  reports five statement mismatches: `partIII_sinTheta_residual_uiNorm`,
  `tanTheta_wholeSpace_paperUINorm_of_crossedDefectsEquivalent`,
  `sinTwoTheta_directedResidual_paperUINorm`, `sinTwoTheta_wholeSpace_paperUINorm`,
  `tanTwoTheta_directedCorner_residual_paperUINorm_exact`. These were unreachable while the
  `Challenge` library did not compile; the build is green as of `5bfa2624`, so they are now
  visible. Repairing them means aligning each challenge statement to the source-faithful
  target, not to whichever production theorem happens to typecheck. Separate task.

## Explicitly out of scope

The infinite-dimensional `U = exp(JΘ)` identity is a broader source-fidelity issue for the
`S1-ui-norms` row and must not be mixed into closing `S2-tan-theta`.
