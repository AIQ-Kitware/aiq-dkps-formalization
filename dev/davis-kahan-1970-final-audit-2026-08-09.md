# Davis & Kahan 1970 (Part III) — final source-first audit

Repository: `/home/joncrall/code/aiq-dkps-formalization` at `10bafe30`
Source: `non-distributable/davis-kahan-1970-modernized-transcription.tex` (paper body lines 161–2948)
Census under test: `dev/davis-kahan-1970-full-source-census.json` (`base_commit ee44c0d7`, behind HEAD)

**Evidence base.** `lake build` at `10bafe30` exits `0` ("Build completed successfully, 9552 jobs"),
with **zero** `declaration uses ...` warnings in the replayed log. All 368 declaration names listed in
the census resolve against `DavisKahan.All` (`MISSING COUNT 0`, sentinel `PROBE-A-COMPLETE`).
Every headline theorem audited is axiom-clean (`[propext, Classical.choice, Quot.sound]`); no
`sorryAx` was found anywhere in scope, in any section.

**Probe files run: 62** — 10 by me (Sections 1, 2, 7, 10 and cross-cutting), 7 (Section 3),
16 (Sections 4–5), 11 (Section 6 + Appendix), 11 (Section 8), 7 (Section 9). Every probe carried an
`example : True := trivial` sentinel and the reported ones exited 0, so no probe was blind.

**Coverage: all ten sections plus the Appendix to Section 6 were examined.** Nothing was left
unexamined.

---

## 1. Headline verdict

**"Remaining Davis–Kahan 1970 completion obligations: none" is NOT true right now.**

This is a large, serious and largely honest formalization — the mathematics is real, the axiom
hygiene is perfect, and the census is far better than it was earlier in the campaign. But printed
conclusions of the headline theorems are still missing, and every section from 3 onwards carries
further gaps. What stands between the repository and that statement, in descending order:

### (A) The `tan 2θ` theorem's ambient conclusion `δ‖tan 2Θ‖ ≤ 2‖H‖` is ABSENT

The paper (L774–781) asserts **two** inequalities. Every compiled `tan 2Θ` endpoint bounds the
**directed** object `tan 2Θ₀` by **`2‖H‖`**, which is weaker than *both* printed conclusions:

* the ambient `tan 2Θ` carries each `tan 2θ_k` **twice** (once from `Θ₀`, once from `Θ₁`), the
  directed object once, so `‖tan 2Θ‖ ≥ ‖tan 2Θ₀‖`, strictly for Ky Fan `ν ≥ 2`;
* `‖R‖ = ‖B‖ ≤ ‖H‖` for every unitarily invariant norm when `H` is off-diagonal.

Verified by elaboration and by reading the definitions:
`tanTwoAngleOperatorC U V h := sinTwoAngleOperatorC U V ∘L (cos 2Θ + P_{Uᗮ})⁻¹`, and
`sinTwoAngleOperatorC U V := 2 • (sinAngleOperatorDirectedC U V * cosAngleOperatorC U V)` with
`sinAngleOperatorDirectedC U V := |P_{Vᗮ} P_U|` — range inside `U` (the repo's own compiled
`range_sinTwoAngleOperatorC_le`). `paperTanTwoThetaRepresentative : U →L[ℂ] Uᗮ` and
`doubleAngleTangentOperator : E0 →L[ℂ] E1` are rectangular, i.e. `Θ₀`-shaped. The branch-free
endpoints `tanTwoTheta_branchFree_bounded_paperUINorm_complex` / `_real` state the representative
condition as `approximationSingularValue (π n) tanTwoTheta = absDoubleAngleTangent
(approximationSingularValue n T)` for a rearrangement `π : ℕ ≃ ℕ` — one copy of each value, i.e.
`Θ₀`.

**There is no ambient `tan 2Θ` object in the repository at all**: `grep` for `paperTanTwoAngle*`
returns nothing, and no `cfc` of `fun t => Real.tan (2 * t)` exists.

This is a *pointed* omission, because the same axis was closed for the other three theorems: the
ambient `sin 2Θ` object `paperSinTwoAngleOperatorC := cfc (sin 2·) (arcsin |P_U − P_V|)` was
introduced on 2026-08-08 and its half proved (`sinTwoTheta_ambient_bounded_paperUINorm_complex`); the ambient
`tan Θ` object `paperTanAngleOperatorC := cfc Real.tan (arcsin |P_U − P_V|)` was introduced and its
half proved yesterday (`tanTheta_ambient_bounded_paperUINorm_complex_of_transversality`). The paper's own §7 proof says "The
whole-space estimate follows by Lemma 6.1" — and `lemma6_1`, `lemma6_1_converse` and `lemma6_2` are
all compiled and EXACT.

**Actionable:** define `paperTanTwoAngleOperatorC := cfc (fun t => Real.tan (2*t)) (paperAngleOperatorC U V)`
(or its branch-free modulus `cfc (|tan(2·)|)`), prove the block-representative modulus identity in the
style of `paperTanAngleOperatorC_eq_modulus_blockRepresentative` /
`paperTanBlockRepresentative`, and pinch against `H` with `lemma6_1` + `paperDiagonalPair_all_kyFan_le`.
That is exactly the route `TanThetaWholeSpace.lean` used yesterday.

Census row **`S2-tan-two-theta`** is `compiled_exact` with `next_action`: *"No mathematical gap and
no recorded scope gap."* **That is wrong.**

### (B) The `tan 2θ` residual conclusion `δ‖tan 2Θ₀‖ ≤ 2‖R‖` exists only in selected-branch form

`DavisKahan.sharp_paperUnitaryInvariantNorm` gives `d · N(tan 2Θ₀) ≤ 2 · N(B01)` — the printed
residual constant — over arbitrary complex Hilbert spaces and every `PaperUnitaryInvariantNorm`. But
it takes the contractive Riccati solution `‖X‖ < 1` as data, i.e. `Θ < π/4`, which is Theorem 8.1's
*conclusion for a particular `Q`*, not a §2 hypothesis; and `_selectedBranch` produces such an `X`
only under the extra smallness `2‖B01‖ < d`, which the paper does not assume. The branch-free
endpoints, which correctly avoid all of that, bound by `2‖H‖` instead of `2‖R‖`. The census records
this observation inside `S2-tan-two-theta`'s notes ("the new endpoints are the PERTURBATION form
`2·N(H)`, not the residual form `2·N(R)` of the printed (DK-tan2)") and then closes the row anyway.

### (C) Real scalars — a genuine, wide, and *measured* gap

Standing assumption 1 of the transcription (L202) is "real or complex". Measured by elaboration:

| family | real endpoint? |
|---|---|
| `sin θ` (§2, Prop 6.1, Thm 6.1, Thm 6.2, appendix common-domain forms) | **YES** — `sinTheta_paperData_real`, `Theorem6_1_real`, `Theorem6_2_real`, `Proposition6_1_real`, `Theorem6_{1,2}_real_common{Domain,Core}`, all `[InnerProductSpace ℝ]`, no `[FiniteDimensional]` |
| `tan 2θ` | **YES** — `tanTwoTheta_branchFree_bounded_paperUINorm_real`, `paperFaithful_tanTwoTheta_uiNorm_real` |
| `tan θ`, both halves | **NO** — `ℂ` only. `Theorem6_3` is `[RCLike]` but `[FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]`; no infinite-dimensional real tan θ declaration exists at all |
| `sin 2θ`, both halves | **NO** — `ℂ` only |
| Theorem 5.1, 5.2, (5.1), Lemma 5.1 | **YES / more general** (`NontriviallyNormedField`, `RCLike`, plus explicit `…_real` twins) |
| Section 3 (every canonical-object result) | **NO** — `ℂ` only |
| Section 4 infinite-dimensional forms | **NO** — `ℂ` only |
| Section 8 (all of it) | **NO** — `ℂ` only |
| Section 9 (the beam) | **NO** — `BeamL2 = Lp ℂ 2`, but the paper's space is real `L²(0,1)` |

**Which rows the complexification machinery would actually close, and who has used it.** Measured by
grep and elaboration:

* **Used**: `DavisKahan/SpectralTheory/Complexification/` is consumed by the §7 real lift
  (`TanTwoThetaBranchFreeInfiniteReal.lean`) and by the real angle-operator layer
  (`Geometry/Angle/OperatorAngleReal.lean`). `complexifySubmoduleEquiv`,
  `PaperUnitaryInvariantNorm.gauge_complexify` and `FormTransport.lean` exist and work — the route is
  *demonstrated*, not hypothetical.
* **Not used at all**: **Section 3** (`Frontier/Section3.lean`, `Geometry/Polar/*`,
  `Geometry/Halmos/*` — zero occurrences of `Complexification`/`complexify`), **Section 4**
  (`Sources/DavisKahan1970/Section4*.lean`, `MathAhead/Section4/*` — zero), **Section 6's tan θ side**
  (its real sin θ forms were proved natively, not transported), and **all of Section 8** (zero).
* **`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Complexification/SpectralDescent.lean` is
  ORPHANED.** `grep -rn "SpectralDescent" --include=*.lean .` returns nothing, and
  `#check @TauCeti.LinearPMap.realSpecProjection` after `import DavisKahan.All` fails with
  `unknownIdentifier`. It compiles only because the `ForTauCeti` lib globs; no `DavisKahan` module
  can see it.
* **Would close**: the `tan θ` rows (`S2-tan-theta`, `DK-6.3-thm`, `DK-6-appendix`), the `sin 2θ` rows
  (`S2-sin-two-theta`, `DK-7-sin2-proof`), Section 4's infinite-dimensional rows, Section 8's (ii)/(iii)
  and 8.2's operator-norm content, and Section 3's *equational/canonical* rows ((3.8), Prop 3.3 both
  directions, Cor 3.2, the Prop 3.5 commutations, Props 3.1/3.2 existence–uniqueness), because the
  direct rotation is a canonical polar factor and both polar decomposition and CFC commute with
  complexification.
* **Would NOT close**: **Theorem 3.1 and Corollary 3.1**, which classify pairs *up to isometric
  equivalence* — a unitary equivalence of complexified pairs need not commute with the real
  conjugation, so it does not descend. Those need a conjugation-equivariant classification.
  **Theorem 8.1(a)/(b)** are also not mechanical: (a) is an `iff` about spectral subspaces of a real
  self-adjoint operator and (b) constructs one, so after complexifying one must show the complex
  branch *is* the complexification of a real reducing subspace.

### (D) Section 3's `IsAcute` is not Definition 3.2, and `J` does not exist

`#print TauCeti.DavisKahan.IsAcute` gives `subspaceGap U V < 1`, i.e. `‖P_U − P_V‖ < 1` (I verified
this myself). The printed Definition 3.2 (L847–849) is `PH ∩ Q̃H = 0 ∧ P̃H ∩ QH = 0`, strictly weaker
in infinite dimensions (angles accumulating at `π/2` with none equal to it). The printed predicate
exists as `TauCeti.IsAcute` (`ForTauCeti/.../AngleGeometry.lean:142` — I elaborated both), and only
`gap ⇒ printed` is proved (`isAcute_of_projectionGap_lt_one`). The docstring at `AngleGeometry.lean:202`
promises a converse `projectionGap_lt_one_of_isAcute` that **does not exist** (`#check` fails,
grep finds only the docstring). Every infinite-dimensional Section 3 result — Props 3.1, 3.4, 3.5,
Cor 3.2 — is stated on the narrower predicate.

Separately, **there is no `J` operator anywhere in the repository**, so §3's `S₀ = J₀ sin Θ₀`,
`J = [[0,−J₀*],[J₀,0]]`, and `U = cos Θ + J sin Θ = exp(JΘ)` (i.e. equation (1.18)) are unformalized,
and with them "Θ commutes with J", "Θ commutes with U", and Corollary 3.2's printed form.

### (E) Section 9's individual-eigenvector conclusions are still certificate-relative

`S9.TheoremOutputCertificate` and `S9.NumericalExampleCertificate` are **never constructed anywhere**,
and a probe proved them *vacuously* inhabitable (`third_eigenvalue := 501`, every output field closed
by `le_refl`/`linarith`, axiom-clean). Equations (9.7) and the two 2-norm sums, and the final `ω₁, ω₂`
bounds, are stated relative to those free reals. (9.1)–(9.4), (9.5), (9.6) and **both lines of (9.8)**
*are* genuinely derived from `beamOperator`.

---

## 2. Section-by-section table

### Section 1 — notation and unitarily invariant norms (`S1-block-residual`, `S1-ui-norms`)

Both rows are `compiled_general_infrastructure` blocked by `exact-source-wrappers`. **Honest.**

| Source | Lean | Verdict |
|---|---|---|
| Ky Fan's theorem, "all UI norms ⟺ all `ν`-norms" (L646) | `…ExactSinTheta.PaperUnitaryInvariantNorm.prefixGauge_le_of_all_kyFan_le_hetero` (⇐), `…all_mul_kyFan_le_of_every_paperNorm_gauge_le` (⇒) | EXACT for the paper's use |
| (1.13) `‖K‖_ν ≥ Re Σ y_k*Kx_k` | `…re_sum_inner_map_le_kyFanApproximationGauge` | EXACT (direction used) |
| "arbitrary unitarily invariant norm" | `PaperUnitaryInvariantNorm` (normalized, zero-pad-coherent family of finite UI seminorms — von Neumann's symmetric gauge, with Fan dominance *proved*); `KyFanDominantIdealFamily` (Gohberg–Krein symmetrically normed ideal, with Fan dominance *assumed as a field*) | Both faithful; see §5 caveat |
| `‖P − Q‖ = ‖sin Θ‖`, all norms (L697) | `paperSinAngleOperatorC_eq : cfc sin (arcsin \|P_U−P_V\|) = \|P_U−P_V\|` | EXACT (operator identity) |
| `‖Q̃P‖ = ‖Q̃E₀‖ = ‖sin Θ₀‖`, all norms | `sinAngleOperatorDirectedC U V := \|P_{Vᗮ}P_U\|` | EXACT by definition |
| `sup{‖Qp−p‖ : p unit ∈ PH} = ‖sin Θ‖₁` (L695) | — | ABSENT |
| `sup inf ‖q−p‖ = 2‖sin ½Θ‖₁` (L696) | — | ABSENT (no half-angle machinery anywhere) |
| Kahan's eigenvalue bound (L465) | — | ABSENT — **external** (Kahan 1967) |

### Section 2 — the four theorems, conclusion by conclusion

Seven printed inequalities:

| # | Printed conclusion | Lean | Verdict |
|---|---|---|---|
| 1 | `sin θ`: `δ‖sin Θ₀‖ ≤ ‖R‖` | `sinTheta` (ℂ), `sinTheta_paperData_real` (ℝ), `Theorem6_1_complex`/`_real` | **EXACT** — real *and* complex, arbitrary dimension, arbitrary UI norm |
| 2 | `tan θ`: `δ‖tan Θ₀‖ ≤ ‖R‖` | `theorem6_3_infiniteTrial_spectral_exists` / `…_of_formBounds_exists` (arbitrary trial subspace, `[CompleteSpace ↥Z]` only), `theorem6_3_generalizedTanTheta_equalRank_spectral` | NARROWER: `ℂ` only |
| 3 | `tan θ`: `δ‖tan Θ‖ ≤ ‖H‖` | `tanTheta_ambient_bounded_paperUINorm_complex_of_transversality`, core `…_all_kyFan` | NARROWER: `ℂ` only; **plus an added `‖sinAngleOperatorC U V‖ < 1`** |
| 4 | `sin 2θ`: `δ‖sin 2Θ₀‖ ≤ 2‖R‖` | `sinTwoTheta_unbounded_reflectionResidual_arbitraryRepresentative_complex` (constant **1**, matching the paper's own proof) | NARROWER: `ℂ` only |
| 5 | `sin 2θ`: `δ‖sin 2Θ‖ ≤ 2‖H‖` | `sinTwoTheta_ambient_bounded_paperUINorm_complex`, `…_all_kyFan` | NARROWER: `ℂ` only |
| 6 | `tan 2θ`: `δ‖tan 2Θ₀‖ ≤ 2‖R‖` | `sharp_paperUnitaryInvariantNorm`, `…_selectedBranch` | NARROWER: `ℂ`; **selected branch** — see headline (B) |
| 7 | `tan 2θ`: `δ‖tan 2Θ‖ ≤ 2‖H‖` | — | **ABSENT** — see headline (A) |

On row 3's acuteness hypothesis: `Real.tan` is total in Mathlib, so `cfc Real.tan Θ` exists
unconditionally and `‖sin Θ‖ < 1` is what makes it *the* tangent. The census argues that under the
Lean statement's asymmetric hypotheses the directed gap controls only `‖P_{Vᗮ}P_U‖`. But the paper's
`tan θ` theorem sits under §3's *standing* assumptions (1.5)+(3.5) (declared at L961), under which
`Θ₀` and `Θ₁` have the same nonzero spectrum, so `‖sin Θ‖ = ‖sin Θ₀‖ < 1` follows from the theorem's
own conclusion. The Lean statement drops those standing assumptions and replaces them with uniform
transversality — defensible, but it is a difference from the printed hypothesis list, and the
directed analogue *is* derived (`isTransverse_of_tanThetaIntervalGap`), so the ambient one should be too.

Other Section 2 claims:

| Source | Lean | Verdict |
|---|---|---|
| "constants in all four theorems best possible" (L764) | `sinTheta_model_equality`, `tanTheta_model_equality`, `tanTwoTheta_model_equality` (each for **every** UI seminorm on the plane); `sinTwoTheta_model_operatorNorm_equality`; `sinTheta_constant_optimal`, `sinTwoTheta_constant_optimal` | NARROWER: the `sin 2θ` equality model is **operator-norm only** |
| "equality attained simultaneously for all UI norms, by direct sums of 2-dim examples" (L765) | the three all-UI-norm plane models | NARROWER: three of four families in dim 2; the direct-sum extension is not formalized |
| "for `ε→0` the four conclusions agree asymptotically" (L768) | `single_double_sine_tangent_ratios_tendsto_one` | acceptable rendering |
| unbounded extension of all four (L771–781) | `sinTheta_generalized_bundled_complex`; `sinTwoTheta_unbounded_perturbation_arbitraryRepresentative_complex`; `theorem6_3_unbounded_infiniteTrial_ideal_exists_of_reducing` | NARROWER: `tan 2θ` unbounded exists only as `tanTwoTheta_unbounded_residual_opNorm_complex`, a **pointwise operator-norm** residual statement. Census `S2-unbounded-scope` records this correctly (`compiled_specialization`) |

### Section 3 — separation of two subspaces

| Source | Lean | Verdict |
|---|---|---|
| Def 3.1 | `Frontier.IsPaperDirectRotation`, `DavisKahanTheory.directRotation` | NARROWER: clause (i) `C_j ≥ 0` rendered as numerical-range accretivity `0 ≤ re⟪x,PTPx⟫`, strictly weaker over ℂ (module docstring concedes it); RCLike form is `[FiniteDimensional]` |
| Def 3.2 | `DavisKahan.IsAcute := subspaceGap < 1` | **NARROWER — headline (D)** |
| Prop 3.1 existence / uniqueness | `complex_directRotation`, `complex_directRotation_unique` | EXACT modulo Def 3.2 |
| Prop 3.1 "characterized by (i) alone" | — | **ABSENT**: both compiled characterizations put (ii) or (3.8) on the left of the iff |
| Prop 3.2 existence iff (3.5) | `proposition3_2_exists_iff_crossedDefectsEquivalent` | EXACT |
| Prop 3.2 "It is not unique" | `proposition3_2_parameterized_nonuniqueness` | NARROWER: an injective parameterization, never "two distinct direct rotations exist" |
| Prop 3.2 Remark, bilateral shift | — | ABSENT |
| (3.8), (3.7) | `sq_eq_spectraReflectionProduct`, `complex_directRotation_sq`; `spectraDirectRotation_conjugates_projection` | EXACT |
| Prop 3.3 forward / converse | `proposition3_3_principalSquareRoot_forward_of_nonneg_blocks`; `…_converse` | **EXACT both directions** (strongest rows in §3) |
| Prop 3.4 | `proposition3_4_square_is_reflected_directRotation` | NARROWER: existential over an unnamed pair, witness `(PH, R_Q PH)` not the printed `(Q₋H, QH)`; `C₀² ≥ ½` replaced by a symmetrized form bound; extra `IsAcute` |
| `S₀=J₀ sin Θ₀`, `J`, `U = exp(JΘ)` | — | **ABSENT — headline (D)** |
| Thm 3.1 classification (both directions) | `twoProjection_operator_classification`; `theorem3_1_spectralMultiplicity_classification_complex` | EXACT in substance; separability faithful (L202); invariant repackaged as Halmos summand dimensions + `genericCosineBlock` multiplicity, and the translation is not itself compiled |
| Thm 3.1 realization | `theorem3_1_realization` | NARROWER: input `HalmosAngleDatum` of `(cos₀,sin₀,cos₁,sin₁,J)` — no `Θ`, no `0 ≤ Θ ≤ π/2`, intertwiner *assumed* not produced from equal multiplicity; the only compiled inhabitant is the all-zero-angle datum |
| Cor 3.1 classification | `corollary3_1_compact_defectBlock_angleList_classification` | EXACT (compactness on `P(1−Q)P`, as printed) |
| Cor 3.1 realization (arbitrary decreasing sequence) | — | ABSENT |
| Prop 3.5 `Θ` ↔ `P`, `Q` | `halmosCosineSq_commute_projection`, `…_right` | NARROWER: proved at the `cos²Θ` level; the ambient `Θ` exists only as a `LinearMap` in the finite-dimensional tree |
| Prop 3.5 `Θ` ↔ `J`, `Θ` ↔ `U` | — | ABSENT |
| Prop 3.5 `∠(x,Ux)=θ` | — | ABSENT (`InnerProductGeometry` used nowhere in `DavisKahan/` or `ForTauCeti/`) |
| Prop 3.5 maximal subspace (a)(b)(c) | `fixedCosineSubspace_maximal` | EXACT (the bundled `proposition3_5_fixedAngle_maximal` is narrower) |
| `cos²Θ = PQP + P̃Q̃P̃` | `halmosCosineSq` | definitional, not a theorem |
| Cor 3.2 | `corollary3_2_reversal`, `corollary3_2_sinAngleOperator_symm` | NARROWER: "J ↦ −J" rendered as `U ↦ U*` — a consequence, and `J` does not exist |

### Section 4 — extremal properties of the direct rotation

| Source | Lean | Verdict |
|---|---|---|
| Prop 4.1 form A (∃ orthonormal `v_k` with `∠(v_k,Vv_k) ≥ θ_k`) | — | **ABSENT** |
| Prop 4.1 form B (singular values minimized at `U`) | `Proposition4_1` | NARROWER: `[FiniteDimensional]` (RCLike, so real+complex) |
| Prop 4.1 form B at printed scope | `Proposition4_1_infiniteDimensional` | NARROWER: `ℂ` only, but no `[FiniteDimensional]`, no compactness |
| `λ_k = 2 sin(θ_k/2)` | `Proposition4_1_directRotationValues` | EXACT up to an unstated trig identity: value is `√(2(1−cos θ_k))`; no lemma rewrites it as `2 sin(θ_k/2)` |
| Cor 4.1 | `Corollary4_1`; and `Frontier.Section4.corollary4_1_restrictedDisplacement_idealGauge` (**in the default build**, axiom-clean) | NARROWER: finite-dim RCLike / infinite-dim ℂ |
| Prop 4.2 | `MathAhead.Section4.sum_displacementAngleSineSq_ge{,_of_mem}`, `tsum_…_of_mem` | NARROWER **two ways**: `ℂ` only, and **the RHS `Σ(1 − ‖C b_i‖²)` is never identified with `Σ sin²θ_k`** — no lemma connects `spectraOperatorAbsoluteValue (spectraCanonicalIntertwiner U V)` to `principalSines`. The docstring's claim is prose |
| Prop 4.3 | `Proposition4_3`, `Proposition4_3_infiniteDimensional` | NARROWER: finite-dim RCLike / infinite-dim ℂ with a Ky Fan-gauge conclusion (which is the *correct* level — pointwise domination would imply the refuted 4.4) |
| (4.1) minimax for `λ_k` | — | ABSENT as a statement |
| (4.3), (4.4), (4.5), (4.6) | — | ABSENT (2×2 block calculus not formalized) |
| Example 4.1, Example 4.2 | — | **ABSENT** — and they matter: they are the paper's own justification for 4.4's `θ ≤ π/3` and real-space restrictions |
| Prop 4.4 | `shortRotation_fullDisplacement_refuted`, `not_davisKahanProposition4_4_Finite` | **Refutation independently confirmed.** Real space, `Θ ≤ π/3`, every UI seminorm, axiom-clean; no theorem form of 4.4 exists. `refuted_as_transcribed` is CORRECT and is **not a gap** |

On `[FiniteDimensional]` in §4: **not defensible as the printed scope.** §4 adopts "the hypotheses of
Theorem 3.1 and Corollary 3.1", and Cor 3.1's hypothesis (L1118–1125) is `PQ̃P` **compact**, not finite
dimension; the parenthetical waives *non*compactness, and Props 4.1/4.2 are stated over `v₁,v₂,…`,
`λ₁≥λ₂≥⋯`, `Σ_{k=1}^∞`. The census's 2026-08-07 re-audit says exactly this and is correct; the
infinite-dimensional aliases exist and are build-guarded, so the mitigation is real.

### Section 5 — the equation `AX − XB = C`

| Source | Lean | Verdict |
|---|---|---|
| Thm 5.1 (Banach, any compatible norm) | `banach_sylvester_lower_bound_uiNorm` = `ContinuousLinearMap.opNorm_le_of_sylvester_of_leftInverse` | **EXACT / more general** (`NontriviallyNormedField`, `NormedSpace`, not even `CompleteSpace`) |
| Thm 5.1 with the paper's literal contraction-compatibility | `Frontier.RemainingSourceSurface.theorem5_1_banach_sylvester` (`CompatibleCrossOperatorNorm`) | **EXACT** (ℂ), axiom-clean, default build |
| Remark: `A`/`B` roles interchangeable (L1607) | — | ABSENT (one-line `symm` companion) |
| Remark: Thm 5.1 encompasses unbounded densely-defined `A` (L1648) | — | **ABSENT** — both Lean forms take `A` bounded. This is a printed claim, not a "left to the reader" |
| (5.1) Hermitian / HS norm / distance-only separation | `…ExactSinTheta.paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap` + real companion | **EXACT / more general** — and **not listed on any census row** |
| (5.2) `‖C‖₁√(rank C) ≥ δ‖X‖₁` | — | ABSENT (nearest brick is a `√dim`, not `√rank`, bound) |
| The 2×2 counterexample showing constant 1 too small | — | ABSENT |
| Thm 5.2 (semibounded self-adjoint, both possibly unbounded, every UI norm) | `Theorem5_2`; real: `davisKahan1970_sylvester_real`, `real_unbounded_sylvester_kyFan` | **EXACT** over ℝ *and* ℂ; `FormBoundedSylvesterGap.leftAboveRightBelow` **is** the printed `A ≥ γ+δ > γ ≥ B` |
| Lemma 5.1 | `Lemma5_1` | **EXACT / more general** (arbitrary filtered net, `RCLike`) |

### Section 6 and the Appendix to Section 6

| Source | Lean | Verdict |
|---|---|---|
| Lemma 6.1, and its converse | `lemma6_1`, `lemma6_1_converse` | **EXACT**, in fact more general; the equisingularity hypothesis is genuinely present |
| Lemma 6.2 | `lemma6_2` | EXACT |
| (6.1) | `PaperSymmetricSinThetaProblem.forward_all_kyFan` / `.reverse_all_kyFan` | EXACT |
| `sin θ` proof/conclusion | `sinTheta`, `sinTheta_paperData_real` | EXACT |
| 2×2 counterexample to `δ‖sinΘ‖ ≤ ‖H‖` (L1815) | `paperOneGap_does_not_imply_symmetric_square_estimate` + the two norm computations | NARROWER: the arithmetic (`√3 < 2·1`) is certified, but `paperCounterexampleA` (`diag(0,1)`) is **defined and never used** — nothing verifies `spec(A₀)={0}`, `spec(Λ₁)={2}`, or that the subspaces are the claimed eigenspaces. The numbers are proved; the hypotheses that make it a counterexample are not |
| Prop 6.1 | `Proposition6_1_complex`, `Proposition6_1_real` | **EXACT**, genuinely ambient (`\|P_U−P_V\|`), both gap directions as separate fields, no `[FiniteDimensional]` |
| Thm 6.1 | `Theorem6_1_complex`, `Theorem6_1_real` | **EXACT** (`E₀` non-isometric via `LowerFrameBound`, no dimension hypothesis, arbitrary same-singular-value representative, arbitrary UI norm) |
| Thm 6.2 | `Theorem6_2_complex`, `Theorem6_2_real` | EXACT |
| Thm 6.2's rank variant `δε‖sinΘ₀‖₁ ≤ ‖R‖₁√(rank R)` | `PaperTheorem62Data.operatorNorm_result_across_of_rank_le` + real twin | EXACT — **not listed on `DK-6.2-thm`** |
| (6.2)–(6.5) direct-rotation block form | — | ABSENT as such, deliberately (the Lean tan θ proofs avoid direct-rotation coordinates) |
| (6.6) | `theorem63ResidualWitness_scalar` | EXACT |
| `tan θ` directed | `theorem6_3_generalizedTanTheta_equalRank_spectral`, `theorem6_3_all_kyFan_core` | EXACT (acuteness **derived**, `isTransverse_of_tanThetaIntervalGap`) |
| `tan θ` ambient | `tanTheta_ambient_bounded_paperUINorm_complex_of_transversality` | NARROWER (acuteness assumed) |
| Example 6.1 (one-sidedness of `Λ₁` essential) | — | **ABSENT** |
| Thm 6.3 | `Theorem6_3` (`[RCLike]`, real+complex, every rectangular UI seminorm, but `[FiniteDimensional]` on both spaces); `theorem6_3_generalizedTanTheta_source_ideal` (`ℂ`, infinite ambient, `[FiniteDimensional ℂ ↥Z]`) | Split; `A₀ = E₀*(A+H)E₀` faithfully rendered |
| Thm 6.3 at arbitrary trial dimension | `theorem6_3_infiniteTrial_of_formBounds`, `theorem6_3_infiniteTrial_spectral_exists` | **YES** — and it drops `rank Z < rank V` entirely, so the `[FiniteDimensional ℂ ↥Z]` elsewhere is not a real limitation |
| Appendix: sin θ with infinite interval `(−∞,α]` | `FormBoundedSylvesterGap` constructors feeding `Theorem6_1_complex`/`6_2` | EXACT |
| Appendix: bounded continuous extension of `R` on a common dense domain | `Theorem6_{1,2}_common{Domain,Core}` + all four real twins | EXACT |
| Appendix: relaxation of Prop 6.1 | — | **ABSENT** (`PaperSymmetricSinThetaProblem` requires `A B : E →L[ℂ] E`) |
| Lemma 6.3 | `lemma6_3_approximationNumber_leakage_complex`, `lemma6_3_singularValue_leakage_complex` | EXACT (more general) |
| Appendix: full unbounded + noncompact tan θ, (6.7)–(6.11), Γ/Υ truncation | `theorem6_3_unbounded_infiniteTrial_ideal_of_reducing` etc. | **NARROWER — the substantive §6 gap.** The *noncompact* half is done. The *unbounded `A₀`* half is assumed away: `UnboundedTrialBlock.operator : Z →L[ℂ] Z` and `Theorem63TrialData.compression : Z →L[ℂ] Z` are **bounded fields**, so the paper's `Ω(τ)A₀Ω(τ)` truncation — the whole reason (6.10) exists — is not reproduced. Unboundedness is permitted only in the ambient `A`/`Λ₁`. The module doc admits it |
| Closing claim "same method applies Thm 6.3 to unbounded operators" (L2259) | same | NARROWER, same reason; and the rank/dimension side is absent from the unbounded form |

### Section 7 — proofs of the double-angle theorems

| Source | Lean | Verdict |
|---|---|---|
| (7.1)–(7.3), `(A+H)U² = U²(A+XHX)` | `sinTwoTheta_mirrorDefect_eq_perturbationDefect`, `…_le_two_mul` | EXACT |
| (7.4)–(7.5), reflected overlap | `sinTwoTheta_reflectedOverlap_norm` | EXACT |
| `sin 2θ` both halves | `unbounded_sinTwoTheta_{,residual_}uiNorm_representative`, `sinTwoTheta_ambient_bounded_paperUINorm_complex` | see §2 rows 4–5 |
| Remark: `δ‖sin2Θ‖ ≤ 2‖H‖` also from gaps in `A` instead of `Λ` (L2346) | this **is** the form the Lean statement takes (gap on `A` at `U`); the census documents the convention swap | EXACT (equivalent by relabelling) |
| Counterexample: the residual inference is asymmetric (`A = diag(0,δ)`, `H = [[0,1],[1,−δ]]`) | — | **ABSENT** |
| (7.6) and the paired-singular-vector argument | `tanTwoTheta_equation_7_6_approximate`, `paired_singularVector_gap_inequality`, `singularValue_ne_one` | EXACT (branch-free, `RCLike`, dimension-free) |
| `tan 2θ` both halves | see §2 rows 6–7 | one selected-branch, one **ABSENT** |
| The page-34 factor-of-2 slip in the printed residual step | written up in `papers/davis_kahan_prop_4_4_counterexample.tex`; census `S2-sin-two-theta` records it | correctly diagnosed; the constant to keep is 2 |

### Section 8 — interpretation of the double-angle theorems

| Source | Lean | Verdict |
|---|---|---|
| 8.1(a) `Θ ≤ π/4 ⟺ Λ₁ ≥ α+δ ∧ Λ₀ ≤ α`, both directions | `Section8.theorem8_1_maximalAngle_le_iff_spectrumIn` | **EXACT** modulo scalars — a genuine `↔`, over *every* reducing `M` |
| 8.1(b) existence of such a `Q` | `theorem8_1_canonicalBranch` with `Q := boundedSelfAdjointSpectralSubspace (A+H) (Iic α)`; `Theorem81Conclusion` is **inhabited by that theorem** | **EXACT, in fact stronger**: explicit construction not `∃`, *strict* `Θ < π/4`, dimension-free (the paper's proof is finite-dim + "by approximation"), plus uniqueness |
| 8.1(i) two inequalities (`A₁` and `A₀` sides) | `theorem8_1_{upper,lower}CompressionRepulsion_source` | **EXACT** as quadratic forms; both sides present |
| 8.1(ii) + "natural infinite-dimensional extensions" | `theorem8_1_{upper,lower}ApproximationRepulsion_source` (dimension-free) + `…_angle_source` | **EXACT**; the eigenvalue/approximation-number dictionary is compiled, not prose |
| 8.1(iii) every symmetric gauge, both sides | `theorem8_1_{upper,lower}SymmetricGaugeRepulsion_source{,_angle,_angle_rev}` | **EXACT** (quantified over `FiniteSymmetricGauge` with the von Neumann axioms; `[FiniteDimensional]` is the paper's own restriction here) |
| 8.2, inherited `sin 2θ` conclusion | `theorem8_2_sinTwoTheta_{perturbation,residual}_source` | **NARROWER**: operator norm only, where the printed `sin 2θ` theorem is for every UI norm |
| 8.2, the new `Θ < π/4` | `theorem8_2_{perturbationHalfGap,residualHalfGap,branch}_source{,_maximalAngle_lt}` | **NARROWER**: the symmetric-`Θ` form carries `[FiniteDimensional ℂ H]` + `finrank P = finrank Q`. The paper asserts it with no dimension restriction |
| 8.2's appeal to Krein's completion | `Frontier.Krein.exists_selfAdjoint_completion_eq_norm_restriction` | **PROVED, not assumed** — axiom-clean |
| Closing: `sin 2θ` extends to `dim X(E₀) < dim X(F₀)` (L2559) | — | **ABSENT**, and has **no census row** (tracked only inside `S2-sin-two-theta`'s prose) |
| Closing: "no corresponding `tan 2θ` extension is known" | — | correctly not an obligation |
| Closing prose (off-diagonal perturbation moving all eigenvectors must move eigenvalues) | `theorem8_1_upperApproximationRepulsion_source` | EXACT (a reading of (ii)) |

`PerturbationHalfGapBridge` / `ResidualHalfGapBridge` **do** carry the conclusion as a field and are
inhabited only from an extra quantitative hypothesis — but **no source-facing Section 8 theorem takes
a bridge**, so this is not a hidden assumption. All 58 declarations on `DK-8.1-thm`/`DK-8.2-thm`
resolve from `DavisKahan.All` and are axiom-clean: the historic "did not compile at all" pathology is
genuinely gone.

### Section 9 — the numerical example

| Source | Lean | Verdict |
|---|---|---|
| real `L²(0,1)` | `M.BeamL2 = Lp ℂ 2` | NARROWER (complex) |
| `(d/dt)⁴` with four free-end BCs, self-adjoint closure | `M.beamOperator`, `M.beamOperator_isSelfAdjoint` | NARROWER: a **form (bending-energy) realization**; no theorem equates it with the closure of the classical operator on the four-BC domain. The BCs are *derived* for eigenfunctions |
| `H = εt`, `0<ε<100` | `M.beamPerturbation`, `M.beamClamp_eq_self` | EXACT |
| `α₁=α₂=0`, 2-dim kernel | `M.beamOperator_affine_mem_and_zero`, `M.finrank_beamTrial = 2` | EXACT |
| `α₃<α₄<⋯` exist | — | **ABSENT** — nothing proves the positive spectrum is nonempty; `M.beamFiniteDataCertificate` takes `alpha ∈ realSpectrum, alpha ≠ 0` as a *hypothesis* for exactly this reason |
| `cos α^{1/4} cosh α^{1/4} = 1` for `k>2` | `M.exists_characteristic_of_eigen` | NARROWER (only the forward direction at eigenvalue level) |
| all `α_k > 500` | `M.realSpectrum_beamOperator_subset_gap`, `…_sharp` | **EXACT, stronger than printed**, unconditional |
| `w_k`, orthonormality, `E₀` | `M.beamTrial_orthonormal`, `M.beamTrial`, `M.beamTrialIncl` | EXACT |
| `Λ₁ > 500` | `M.beamPerturbed_specProjection_Ioo_eq_zero` | EXACT in substance |
| `A₀ = 0`, `R = HE₀`, `R*R` and its eigenvalues | `M.beamOperator_apply_trial`, `M.beamResidual`, `M.beamResidualGram_matrix`, `S9.residualGram_eigenvalue{High,Low}_charAt` | EXACT, from genuine `L²` integrals |
| **(9.1), (9.2), (9.3), (9.4)** | `M.beamSinTheta_le`, `M.beamSinTwoTheta_lt`, `M.beamSinThetaSum_le`, `M.beamSinTwoThetaSum_lt` composed with `S9.equation_9_1..4` | **EXACT, derived from `beamOperator`** |
| `Â₀`, `R̂`, `E₀*R̂ = 0`, (9.5) | `M.beamRitz_matrix`, `M.beamResidual_inner_trial`, `S9.equation_9_5_{low,high}` | EXACT |
| `R̂*R̂ = (ε²/30)[[1,−1],[−1,1]]` | `S9.recentered_residual_gram_from_affine_moments` | NARROWER: at the affine-moment level only; no beam-side assembly |
| `‖R̂‖₁ = ‖R̂‖₂ = ε/√15` | `M.norm_beamRitzResidual_le` | NARROWER: only `≤`; equality and the 2-norm are absent |
| **(9.6)** `tan θ₁` | `M.beamTanTheta_lt_printed` | **EXACT, unconditional**, via `theorem6_3_unbounded_ideal_directedTangent` |
| (9.6) 2-norm sum | `S9.equation_9_6` applied to a free real | **ASSUMED-VIA-RECORD** (`S9.TheoremOutputCertificate`) |
| **(9.7)** and its 2-norm sum | `S9.equation_9_7` applied to free reals | **ASSUMED-VIA-RECORD**; no `beamTanTwoTheta` exists |
| Weinberger's `sin²φ_k` inequality | appears only as an explicit hypothesis `hweinberger` | **EXTERNAL, correctly hypothesised, never assumed**; `S9.naive_second_scalar_lower_bound_tripwire` proves the naive substitute fails |
| Arrowhead 3×3 and its two lower roots; the `O(ε⁴)` expansion | `S9.ArrowheadThreeByThree`, `S9.exists_weinbergerLowerRootCertificate`, `S9.ritzLow_sub_weinbergerLowerRoots_le` | EXACT, and quantitatively sharper than the paper's prose |
| **(9.8) both lines** | `M.beam_equation_9_8_lower`, `…_upper`, `M.beam_equation_9_8` | **EXACT, unconditional, and confirmed to go through the Theorem 6.3 route, not Weinberger's inequality** |
| `θ₁ ≥ φ_k`, `sin²φ₁+sin²φ₂ = sin²θ₁+sin²θ₂` | — | ABSENT |
| sharper `tan φ_k < (ε/√30)/(500−α̂_k)` | `M.beamTanPhi_{low,high}_le`, `M.norm_beamColumnResidual_{low,high}` | EXACT |
| `ℓ₂` counterexample (`e`, `diag(1,μ⁻¹,…)`, infinite residual, "small change remedies") | `S9.geometricTrial`, `S9.diagonalOperator`, `S9.geometricTrial_notMem_diagonalDomain`, `S9.truncatedTrial_mem_diagonalDomain` | EXACT |
| `α̂ = 1+μ` in that example | — | ABSENT |
| Weinberger's bounds in that example | — | ABSENT (external) |
| `η_k`, `ψ_k`, `ω_k`, `cos ω = cos η cos ψ`, `ω² ≤ ψ²+η²` | `S9.individual_angle_le_exact_envelope{,_of_tangents,_of_subspace}` | **EXACT as general lemmas** (both identities *derived*), but **never instantiated at the beam** |
| (9.9), (9.10), (9.11) | `S9.block_eigenproblem_iff`, `S9.lower_coordinate_eq`, `S9.schur_complement_reduction` | NARROWER: general, uninstantiated |
| `(α̂₂−α̂₁)tan 2ψ_k ≤ 2‖Ĥ‖₁` | `S9.half_tanTwoPsi_ratio_lt{,_of_eigenvalue_upper}` | NARROWER: scalar arithmetic only; the tan 2θ theorem is never applied to `Ĥ` |
| Theorem 8.1 gives `0 ≤ ψ_k < π/4` | — | **ABSENT** — `psi < π/4` is a *hypothesis* of the envelope lemmas |
| `ω₁, ω₂` final bounds | `S9.final_{lower,upper}_individual_angle_bound` | **ASSUMED-VIA-RECORD** (`TheoremOutputCertificate.omega₁/omega₂`) |
| "best possible bound … awaits Question 10.2" | — | not an obligation |

### Section 10 — open questions

| Source | Lean | Verdict |
|---|---|---|
| Q10.1 (distance-only separation) | census cites `Theorem6_2_complex` | The paper poses this as open; Theorem 6.2 is *in the paper*, so it does not "resolve" the question — but Q10.1 is not proof debt either way. Bookkeeping quibble only |
| Q10.2, Q10.3, Q10.4 | — | `not_a_completion_obligation` — **correct**, no debt |
| Added-in-proof bibliographic notes | — | not obligations |

---

## 3. Every gap found, ranked

### (a) Real mathematical obligations of THIS paper

1. **`tan 2θ` ambient half** `δ‖tan 2Θ‖ ≤ 2‖H‖`. Route above (headline A). *Highest priority — it is a
   printed conclusion of a headline theorem and the analogous work exists for the other three.*
2. **`tan 2θ` residual half branch-free**: `δ‖tan 2Θ₀‖ ≤ 2‖R‖` without `‖X‖ < 1` and without
   `2‖B01‖ < d`. The branch-free machinery (`paired_singularVector_gap_inequality`,
   `absDoubleAngleTangent`) is already there; only the right-hand side must be moved from `H` to the
   off-diagonal block.
3. **Section 6 Appendix: unbounded Ritz compression.** Replace `Theorem63TrialData.compression :
   Z →L[ℂ] Z` (and `UnboundedTrialBlock.operator`) with a self-adjoint partial map semibounded above
   by `α`, and reproduce the paper's `Ω(τ)A₀Ω(τ)` truncation with the `‖F‖₁ ≤ ητ ≤ ε` estimate.
   Lemma 6.3 is already available as the leakage input.
4. **Section 3, Proposition 3.1's third clause `(i) ⟹ (ii)`.** The paper's own route (L887–898):
   `C₀²S₁ = S₁C₁²` ⇒ `f(C₀²)S₁ = S₁f(C₁²)` by CFC ⇒ `C₀S₁ = S₁C₁`, then density of `ran C₁`.
5. **Section 3, `J` and the exponential form** `S₀ = J₀ sin Θ₀`, `J`, `U = cos Θ + J sin Θ = exp(JΘ)`.
   Four separate §3 claims (equation (1.18), Θ↔J, Θ↔U, Cor 3.2's printed form) depend on it.
6. **Section 3, Definition 3.2 as printed**, and re-scoping Props 3.1/3.4/3.5 and Cor 3.2 onto it.
   The current proof inverts `|S|` globally; under the printed definition `|S|` is injective with
   dense range but not invertible, so the polar factor must be a unitary extension of a densely
   defined isometry.
7. **Section 4, Proposition 4.2's right-hand side**: prove `Σᵢ(1 − ‖C bᵢ‖²) = Σₖ sin²θₖ`. Until then
   `sum_displacementAngleSineSq_ge` is a true theorem about an unidentified quantity.
8. **Section 4, Proposition 4.1's angle form** (∃ orthonormal `v_k ∈ PH` with `∠(v_k,Vv_k) ≥ θ_k`).
9. **Section 5, inequality (5.2)** and its 2×2 counterexample; and **Theorem 5.1's unbounded-`A`
   claim** (L1648–1649), which the paper states as covered by its own statement and proof.
10. **Section 6, Example 6.1** (one-sidedness of `Λ₁` essential) and the **missing spectral
    certificates for the §6 sin θ counterexample** (`paperCounterexampleA` is dead code).
11. **Section 6 Appendix, unbounded Proposition 6.1** (the appendix explicitly relaxes it;
    `PaperSymmetricSinThetaProblem` is bounded-only).
12. **Section 8, Theorem 8.2's inherited `sin 2θ` conclusion at every UI norm**, restated at 8.2's own
    hypotheses (currently operator norm only).
13. **Section 8, Theorem 8.2's `Θ < π/4` without `[FiniteDimensional]`** — see the census disagreement
    below; the recorded justification for the narrowing is invalid.
14. **Section 8 closing sentence: the `sin 2θ` extension to `dim X(E₀) < dim X(F₀)`** — asserted in the
    paper, formalized nowhere, and with no census row.
15. **Section 9**: beam-side `tan 2θ` for (9.7); Ky Fan-2 tangent sums for (9.6)/(9.7); instantiation
    of (9.9)–(9.11), `ψ_k`, `η_k`, `ω_k` at the beam (the 2-dimensionality prerequisite is already
    proved); `0 ≤ ψ_k < π/4` from `Section8.theorem8_1_canonicalBranch`; existence of `α₃`; and the
    identification of `beamOperator` with the closure of the classical four-BC operator.
16. **Section 3, Theorem 3.1's realization at the `Θ` level** and **Corollary 3.1's realization
    sentence**; **Proposition 3.2's actual nonuniqueness statement** and its **bilateral-shift Remark**.
17. **Section 7's residual-asymmetry counterexample** (`A = diag(0,δ)`, `H = [[0,1],[1,−δ]]`).
18. **Section 2 sharpness**: the `sin 2θ` equality model at every UI norm (currently operator norm
    only), and the direct-sum simultaneous-attainment construction.
19. **Section 4, Examples 4.1 and 4.2**; equations (4.1), (4.3)–(4.6).
20. **Section 1's two "measures of difference" identities** (`sup‖Qp−p‖ = ‖sin Θ‖₁`,
    `sup inf = 2‖sin ½Θ‖₁`) — the paper states them without proof, so lowest priority.

### (b) External mathematics the paper merely cites — NOT gaps

* Kahan's 1967 eigenvalue-perturbation bound (§1).
* Weinberger's angle inequality and the Lehmann/Weinberger "best lower bounds" optimality (§9) — the
  repository correctly carries Weinberger's inequality as an explicit hypothesis and never assumes it;
  (9.8) is closed by the paper's own Theorem 6.3 route, which I confirmed.
* Ky Fan's theorem, von Neumann's theorem, Weyl monotonicity — all present in usable form.
* Krein's self-adjoint completion (§8) — **not external in practice: it is proved here**
  (`exists_selfAdjoint_completion_eq_norm_restriction`, axiom-clean).
* Proposition 4.4 — FALSE as printed, refuted in the build. `refuted_as_transcribed` is correct and
  is **not** a gap. No theorem form has been restored.
* Section 10's Questions 10.2–10.4 — open questions, no debt.

### (c) Scope narrowings worth fixing

* **Real scalars** — headline (C). The largest single axis, ~20 rows, with a demonstrated route and an
  orphaned `SpectralDescent.lean`.
* **`DavisKahan.IsAcute = subspaceGap < 1`** vs printed Definition 3.2 — headline (D).
* **`‖sinAngleOperatorC U V‖ < 1`** in the ambient `tan θ` theorem: a hypothesis the paper's own
  argument forces (the directed analogue *is* derived).
* **`[FiniteDimensional]` on Section 4's scalar-generic forms** — the printed hypothesis is
  compactness of `PQ̃P`, not finite dimension (mitigated: `ℂ` infinite-dimensional aliases exist).
* **Definition 3.1 clause (i)** rendered as numerical-range accretivity rather than operator
  positivity.
* **`KyFanDominantIdealFamily` assumes Fan dominance as a field**, where `PaperUnitaryInvariantNorm`
  proves it. Both are legitimate; the asymmetry means the tan θ side quantifies over a class defined
  by a hypothesis rather than over the paper's construction.
* **Section 9's complex `L²`** and the form-vs-closure identification of `beamOperator`.
* **`λ_k = 2 sin(θ_k/2)`** stated as `√(2(1−cos θ_k))` with no bridging lemma.

### (d) Census bookkeeping errors with nothing wrong underneath

Listed in §4 below; the main ones are stale `next_action`s pointing at files that have moved or been
deleted, declaration lists that under-report what is actually proved, and one mislabelled declaration.

---

## 4. Census disagreements — row by row

Where census prose disagrees with what elaborates, **the build wins**.

1. **`S2-tan-two-theta`** (`compiled_exact`, `next_action`: *"No mathematical gap and no recorded scope
   gap"*) — **WRONG.** The printed ambient conclusion `δ‖tan 2Θ‖ ≤ 2‖H‖` is absent (headline A), and
   the row's own notes concede the residual/perturbation discrepancy (headline B) before closing the
   row anyway. Recommended: `compiled_specialization`, with two recorded axes (ambient `Θ`; residual
   constant branch-free).
2. **`S2-sharpness`** (`compiled_exact`; notes say *"full quartet simultaneous equality remains in the
   Part III campaign"*; `next_action` says *"Proved"*) — internally contradictory, and the notes are
   the accurate half: `sinTwoTheta_model_operatorNorm_equality` is operator-norm only.
3. **`DK-3.2-def`** (`compiled_exact`, *"the predicate is the printed definition"*) — **FALSE.**
   `IsAcute := subspaceGap < 1`; the printed predicate is `TauCeti.IsAcute`, and only one direction is
   proved.
4. **`DK-3.1-prop`** (*"Proposition 3.1 is represented in full … the characterisation biconditional"*)
   — **FALSE** for the "characterized by (i) alone" clause; both compiled characterizations carry (ii)
   or equation (3.8) on the left.
5. **`DK-3.4-prop`** (*"Nothing that is proof debt"*) — **overstated**: existential over an unnamed
   pair, and the witness is not the printed `(Q₋H, QH)`.
6. **`DK-3.5-prop`** (`compiled_exact`, *"Both clauses … are proved"*) — **FALSE.** Prop 3.5 has six
   assertions. The two declarations the row offers (`bounded_angle_commute`,
   `bounded_sinAngleOperatorC_norm`) are neither of the printed commutations. Θ↔J, Θ↔U and the
   eigenvector-angle clause are absent.
7. **`DK-3.2-prop`, `DK-3.1-cor`** (*"Nothing outstanding"*) — incomplete: the bilateral-shift Remark,
   the actual nonuniqueness statement, and Cor 3.1's realization sentence are absent.
8. **`DK-3.1-thm`** (`compiled_exact`) — the classification half is genuinely both-directional and
   correct; `compiled_exact` overstates the **realization** half.
9. **`DK-4.1-cor`** — `scope_gap` says the infinite-dimensional wrapper *"is not yet stated"*. **FALSE**:
   `Frontier.Section4.corollary4_1_restrictedDisplacement_idealGauge` elaborates from
   `import DavisKahan.All`, is axiom-clean, and is in the default build via `DavisKahan.Frontier.All`.
10. **`DK-4.1-prop`, `DK-4.3-prop`** — `next_action` asks to *"promote"* files out of
    `Experimental/MathAhead/Section4/`. Already done; the files are at `DavisKahan/MathAhead/Section4/`
    and are in the build, axiom-clean.
11. **`DK-4.2-prop`, `DK-4.3-prop`** — both carry a dated note asserting the infinite-dimensional form
    *"is `sorry` (`#print axioms` reaches `sorryAx`)"* in `DavisKahan/Experimental/Frontier/Section4.lean`.
    **That path no longer exists** and every Section-4 frontier declaration is axiom-clean.
12. **`DK-4.2-prop`** — its first listed declaration,
    `DavisKahanTheory.directRotation_minimizes_sum_sq_basis_angles`, **is not Proposition 4.2**: it is
    a Frobenius statement about a basis of the *whole space* and the full displacement, a consequence
    of Prop 4.3. The census's "nuclear-norm specialization" gloss for it is also wrong (it is
    Frobenius). And its `scope_gap` wrongly claims the dimension axis is open — the `_of_mem` /
    `tsum_…_of_mem` forms have no `[FiniteDimensional]`; only the real-scalar half is open.
13. **`DK-5.1-thm`** — declaration list omits `Frontier.RemainingSourceSurface.theorem5_1_banach_sylvester`,
    the version carrying the paper's *literal* compatibility axiom. Separately, **no row anywhere claims
    inequality (5.1)**, yet `paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap` and its real
    companion prove it — the census under-claims.
14. **`DK-5.2-thm`** — still lists `blocked_by: ["real-scalar-infinite-dimensional-scope"]`, which
    contradicts its own removed `scope_gap`; the real endpoint `davisKahan1970_sylvester_real` exists.
15. **`DK-6.2-thm`** — omits the printed rank variant, which *is* compiled
    (`PaperTheorem62Data.operatorNorm_result_across_of_rank_le` + real twin).
16. **`DK-6.3-thm`** — omits `TauCeti.DavisKahan1970.Theorem6_3`, the literal source surface, which is
    `[RCLike]`; the `real-scalar-infinite-dimensional-scope` blocker is therefore only half true (the
    real gap is infinite-dimensional only).
17. **`DK-6-appendix`** (`compiled_specialization`) — right status, wrong recorded reason. The actual
    specialization is the **bounded Ritz compression field** (so the paper's `Ω(τ)` truncation of an
    unbounded `A₀` is not reproduced); that blocker is not recorded.
18. **`S2-tan-theta`** — the row does not record that the ambient half assumes
    `‖sinAngleOperatorC U V‖ < 1`, a condition the paper derives.
19. **`DK-8.2-thm`** — the notes' **infinite-dimensional counterexample is not a counterexample**: the
    example (`P := span{e₁,e₂,…} ⊕ 0`, `Q := E ⊕ 0`) violates standing assumption (3.5), declared at
    transcription **L961** ("We shall assume (3.5) as well as (1.5) except where stated otherwise"):
    `dim(PH ∩ Q̃H) = 0` while `dim(P̃H ∩ QH) = 1`. So it does not license the `[FiniteDimensional]` +
    `finrank P = finrank Q` addition, and `next_action: "Nothing outstanding"` is wrong. The
    *mathematics* in the repo is sound; the *justification for the narrowing* is not.
20. **`DK-8.2-thm`** — `compiled_exact` also overstates the norm axis: the conclusion is stated only at
    the operator norm where the printed theorem is for every UI norm. Stale prose in the same row names
    `perturbationHalfGapBridge_of_sourceHypotheses` in namespace `…Section8`, where it does not exist
    (it is in `…Experimental.Frontier.Section8`), and does not mention that it needs an extra
    smallness hypothesis.
21. **`DK-8.1-thm`, `DK-8.2-thm`** — both are `compiled_exact` while being entirely
    `InnerProductSpace ℂ`, which is exactly the defect for which `S2-sin-two-theta` and `S2-sin-theta`
    were graded. Inconsistent grading.
22. **Blocker `section9-certificate-discharge`** — its prose says honest discharge requires the chain
    in `DavisKahan/Experimental/Frontier/Section9Analytic.lean`. **That file was deleted in commit
    `95bbd5ea`.** The same blocker says it still constrains `DK-9.8`, while the `DK-9.8` row carries
    `blocked_by: []` — and the row is right (`M.beam_equation_9_8` is unconditional and axiom-clean).
23. **`DK-9-model`** (`compiled_exact`) — **overstated**: complex not real; a form realization not
    proved equal to the closure of the four-BC classical operator; and `α₃`'s existence unproved
    (which is why `beamFiniteDataCertificate` must take a nonzero spectral point as a hypothesis).
    `compiled_specialization` is the honest status.
24. **`DK-9.5-9.7`** (`compiled_specialization` / `proved_conditional`) — conflates three equations:
    (9.5) is unconditional, (9.6) is unconditional for the genuine beam, only (9.7) and the 2-norm
    sums are certificate-relative. The blanket `proved_conditional` hides that (9.7) is the sole
    obstruction.
25. **`DK-9.1-9.4`** — declaration list omits `S9.equation_9_2` and `S9.equation_9_3`, both load-bearing.
26. **`DK-9-infinite-residual-counterexample`** — does not record that `α̂ = 1+μ` (L2761) is absent.
27. **`DK-10.1`** (`resolved_by_modern_development`, citing `Theorem6_2_complex`) — Theorem 6.2 is *in the
    paper*, so it cannot resolve the paper's own open question. Not proof debt either way; a
    classification quibble.
28. **Missing row**: the last paragraph of Section 8 (L2559, the `sin 2θ` unequal-dimension extension)
    has **no census row** at all; it is tracked only inside `S2-sin-two-theta`'s prose, which makes it
    invisible to any per-row status read.
29. **Non-census stale prose that contradicts the build** (three instances):
    * `DavisKahan/Sources/DavisKahan1970/TanTheta.lean:50` says the general-Hilbert-space
      unitary-invariant-ideal conclusion of Theorem 6.3 *"is not yet compiled"*. It is
      (`theorem6_3_generalizedTanTheta_source_ideal`, `theorem6_3_infiniteTrial_of_formBounds`).
    * `DavisKahan/Geometry/Angle/PaperTanAngle.lean` carries an "## Open obligation" section saying the
      whole-space `tan Θ` estimate *"is **not** proved here"* — landed yesterday in
      `Sources/DavisKahan1970/TanThetaWholeSpace.lean`.
    * `ForTauCeti/Analysis/InnerProductSpace/AngleGeometry.lean:202` promises
      `projectionGap_lt_one_of_isAcute` "below"; it does not exist. Given headline (D) this is the
      highest-risk stale comment in the chain.
30. **Tooling note (not a census row).** `python3 scripts/check_davis_kahan_1970_source_census.py`
    prints *"Census verification: CLEAN — all 48 rows agree with the build"* and
    *"368/368 resolve against DavisKahan.All"*. It verifies **name resolution only**. Every finding in
    this audit is invisible to it. That output is precisely the "CLEAN (48 items)" signal AGENTS.md
    warns about, and should be reworded so a reader cannot mistake it for a scope check.

**I made no edits to the census or to any file.** No claim in it was demonstrably *false about the
mathematics* in a way that required an in-place correction; the errors above are status/scope
over-claims, stale prose and omissions, which the human should adjudicate.

---

## 5. What I could not determine

* **Whether the printed Theorem 8.2 (`Θ < π/4`) is true in infinite dimensions under (1.5)+(3.5).**
  The paper's step "`β ≤ A₀ ≤ α` implies `P = PQ(1)`, so `θ(1) ≥ Θ`" controls only the directed gap;
  the symmetric `‖P − Q(0)‖` needs the other direction. (3.5) rules out exact-`π/2` intersections but
  I could not see that it forces the two directed gaps to agree, and I did not construct an example
  satisfying (3.5) with unequal directed gaps. This decides whether the repository's
  `[FiniteDimensional]` is a correct repair or an avoidable weakening.
* **Whether `Σᵢ(1 − ‖C bᵢ‖²)` in Proposition 4.2 really equals `Σ sin²θ_k`.** Mathematically it should
  (it is `dim U − tr((C|_U)²)`), but there is no Lean lemma; I can report the identification as
  unproved, not as false.
* **Whether the complexification machinery actually closes Section 8.** I confirmed it is unused there
  and gave the structural reason 8.1(a)/(b) are harder than a norm transport, but I did not attempt
  the transport.
* **How much of "every unitarily invariant norm" is *reachable* through `KyFanDominantIdealFamily`.**
  Instances exist (`operatorNorm`, `kyFan k hk`) so the results are not vacuous, but I did not
  enumerate Schatten-`p`/trace-class instances. On the `sin θ` side this does not arise, because
  `PaperUnitaryInvariantNorm` *derives* Fan dominance.
* **Whether `beamOperator` is the closure of the classical four-BC operator.** Nothing in the build
  states it; I report only that the identification is not formalized and that the BCs are recovered
  for eigenfunctions.
* **Whether Section 9's missing beam-side `tan 2θ` is blocked or merely unwritten.** The repository has
  unbounded `tan 2Θ` results, but I did not check whether their hypotheses are satisfiable by
  `beamTrialBlock ε`.
* **Whether `TauCeti.DavisKahan.IsAcute` and printed Definition 3.2 differ on any pair actually
  occurring in this development.** They are provably different predicates; I found no compiled
  counterexample pair, and constructing one was outside a read-only audit.
* **Whether `theorem3_1_realization` is non-vacuous at a nonzero angle.** The only compiled inhabitant
  of `HalmosAngleDatum` is the all-zero-angle one.
* **Whether `Theorem6_3`'s finite-dimensional route and the infinite-dimensional `theorem63Compression`
  route are formally linked.** They live in different files with different data records; I found no
  bridging theorem.
* **Whether `DavisKahan.Experimental.All` still compiles.** Its `.olean` is stale (incompatible header,
  presumably from the `v4.33.0-rc2` bump). It is not a default target and nothing in this audit
  depended on it — all census declarations resolve from `DavisKahan.All` — but I did not rebuild it.
