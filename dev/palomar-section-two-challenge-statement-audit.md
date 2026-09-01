# Palomar Section 2 Challenge: clause-by-clause statement audit

**Date.** 2026-08-31.
**Subject.** `dev/palomar-candidate/Challenge.lean` and `dev/palomar-candidate/Solution.lean`.
**Question.** Does each printed Davis–Kahan Section 2 clause appear in the Challenge at
its printed scope, with its own hypotheses, and with a quantity that is the one the
source names?

This is a *statement* audit of the compact Palomar vocabulary. It is deliberately
separate from `scripts/check_davis_kahan_1970_result_inventory.py` and from the
29-result census: the production census governs the production endpoints, and
nothing here reopens it. A defect below is a defect in the new Challenge
vocabulary, not in the development.

**Sources compared against.**

1. `prose/distilled_literature/DavisKahan1970_part_III.tex`, blocks `S1-block-residual`,
   `S1-ui-norms`, `S2-sin-theta`, `S2-tan-theta`, `S2-sin-two-theta`,
   `S2-tan-two-theta`, `S2-unbounded-scope`.
2. `dev/davis-kahan-1970-result-semantic-review-2026-08-31.md` (the hostile result audit).
3. The canonical fixed-field production witnesses listed in
   `DavisKahan/Sources/DavisKahan1970/SectionTwo.lean`.

---

## 0. Two facts from Section 1 that decide most of the scope rows

**(a) Neither decomposition is assumed spectral.** `S1-block-residual` says in as many
words: *“No assumption is made here that `P` or `Q` is a spectral projector or that the
two diagonal spectral sets are disjoint.”* The theorems then add a separation hypothesis
on the two blocks. So the source scope of every ambient clause is **an arbitrary reducing
decomposition whose blocks are separated**, not a spectral selection. A separated
reducing decomposition *is* spectral — that is a theorem, not a hypothesis, and stating
it as a hypothesis narrows the printed result.

**(b) The trial block may be unbounded.** `S2-unbounded-scope` says the results are
intended for unbounded self-adjoint `A`, and that *useful* conclusions need the
perturbation or **residual** to extend boundedly — the residual, not the compression.
`(1.8)` defines `R = (A+H)E₀ − E₀A₀` with `A₀` the trial/Ritz operator, which for
unbounded `A` is unbounded. So the source scope of the trial data is: **partial-map
compression, bounded residual.**

Both are now respected by the Challenge; neither was in the first draft.

---

## 1. `S2-sin-theta` — one printed clause

| | |
| --- | --- |
| **paper clause** | `spec(A₀) ⊂ [β,α]`, `spec(Λ₁) ∩ (β−δ, α+δ) = ∅` (or interchanged) ⟹ `δ‖sin Θ₀‖ ≤ ‖R‖` |
| **Challenge** | `theorem sinTheta` |
| **production witness** | `DavisKahan1970.sinTheta_unbounded_formGap_paperUINorm_rclike` |
| **correspondence** | `Solution.sinTheta_proof` — **proved**, with no capability binder |
| **real/complex** | `[RCLike 𝕜]` ✓ |
| **bounded/unbounded** | `A : E →ₗ.[𝕜] E`, `A₀ : F →ₗ.[𝕜] F`, `Λ₁ : G →ₗ.[𝕜] G` — all partial maps ✓ |
| **dimension** | arbitrary ✓ |
| **norm** | `UINorm`, `= PaperUnitaryInvariantNorm` by `UINorm.toPaper`, values agree by `rfl` ✓ |
| **gap** | `SylvesterGap`, three constructors, both half-infinite configurations ✓ |
| **RHS quantity** | `N.norm R`, `R` the printed residual of `IsTrialResidual` ✓ |
| **angle multiplicity** | directed, once: `directedSine E₀ F₀ = (I − F₀F₀⋆)E₀`, the source's own `Q^⊥E₀` ✓ |
| **constant** | `1` ✓ |
| **status** | **exact**; unchanged from the first draft, and deliberately not churned |

---

## 2. `S2-tan-theta` — two printed clauses

Shared source data in the Challenge: `A` self-adjoint, `V` reducing `A`, and the ordered
separation `A|Vᗮ ≥ α + δ` in form.

### 2a. directed — `δ‖tan Θ₀‖ ≤ ‖R‖`

| | |
| --- | --- |
| **paper clause** | `δ‖tan Θ₀‖ ≤ ‖R‖`, `Θ₀` the angle between trial and exact subspaces, `R` the Rayleigh–Ritz residual |
| **Challenge** | `TanThetaResult.directed` |
| **production witness** | `tanTheta_directed_unboundedRitz_paperUINorm_complex` / `…_real` (2026-08-31; the previously named `…_unboundedTrial_…` pair carries a **bounded** compression and is now a specialization — see `dev/davis-kahan-1970-result-semantic-review-2026-08-31.md`, F9) |
| **correspondence** | **not carried out** |
| **real/complex** | `[RCLike 𝕜]`; production fixed-field |
| **bounded/unbounded** | `RitzData.compression : U →ₗ.[𝕜] U` — partial map ✓ (production: `UnboundedRitzPair`, whose `trial.compression : Z →ₗ.[𝕜] Z` is also partial ✓) |
| **dimension** | arbitrary ✓ |
| **norm** | `UINorm` ✓ |
| **gap** | ordered, `SemiboundedAbove D.compression α` and `SemiboundedBelow (block A Vᗮ) (α+δ)`; production uses `specProjection (Ioo α (α+δ)) = 0` on a **spectral** `V` |
| **RHS quantity** | `N.norm D.residual` — the residual alone; **no `N.Finite H`** ✓ |
| **angle multiplicity** | directed, once: `tanSeq (directedSineBlock U V)`, `directedSineBlock U V = P_{Vᗮ}∘ι_U` — the same operator as production's `theorem63DirectedSineBlock` ✓ |
| **constant** | `1` ✓ |
| **status** | **proved, at arbitrary `[RCLike 𝕜]`** (`Solution.tanTheta_directed_proof`). Both obligations this row carried are discharged as of 2026-09-01. (i) *`V` reducing, not spectral* — the production endpoint takes `ReducingComplement A V`, and `ReducingComplement.ofReducesSubspace` builds it from the Challenge's `Reduces A V`; there was never a spectral selection in this clause. (ii) *the representative and the pole* — `tanTheta_directed_unboundedRitz_paperUINorm_exists_complex` exhibits a representative with exactly the paper's approximation numbers and derives `∀ n, aₙ(sin Θ₀) < 1` from the two form bounds, neither assumed. `Solution.tanTheta_directed_proof_complex` **is** this Challenge clause over `ℂ`, all three conjuncts. What remains is the scalar field alone. |

### 2b. ambient — `δ‖tan Θ‖ ≤ ‖H‖`

| | |
| --- | --- |
| **paper clause** | `δ‖tan Θ‖ ≤ ‖H‖`, `Θ` the ambient angle, `H` the whole perturbation, under `H₀ = 0` |
| **Challenge** | `TanThetaResult.ambient` |
| **production witness** | `tanTheta_ambient_unboundedRitz_paperUINorm_complex` / `…_real` |
| **correspondence** | **not carried out** |
| **real/complex** | `[RCLike 𝕜]`; production fixed-field |
| **bounded/unbounded** | `RitzData` partial compression ✓ (production: `UnboundedRitzPair`, matching field for field — `Solution.RitzData.toUnboundedRitzPair` is **proved**) |
| **dimension** | arbitrary ✓ |
| **norm** | `UINorm` ✓ |
| **gap** | ordered; production's `hUnwanted` is the same form bound, its `ReducingComplement A V` is implied by the Challenge's `Reduces A V` |
| **RHS quantity** | `N.norm H` — its own hypothesis `N.Finite H`, not shared with 2a ✓ |
| **angle multiplicity** | ambient, twice: `tanSeq (ambientSine U V)`, `ambientSine U V = P_V − P_U`. Production concludes on `paperTanAngleOperatorC U V = cfc tan (cfc arcsin (modulus (P_U − P_V)))`, whose approximation numbers are `tan(arcsin sₙ(P_U − P_V))` ✓ |
| **constant** | `1` ✓ |
| **status** | **proved, at arbitrary `[RCLike 𝕜]`** (`Solution.tanTheta_ambient_proof`). `Solution.tanTheta_ambient_proof_complex` **is** this Challenge clause over `ℂ`, all three conjuncts. Three pieces came together on 2026-09-01: `DavisKahan1970.approximationNumber_paperTanAngleOperatorC` identifies the operator's approximation numbers with the Challenge's sequence; `Solution.evalSeq_tanSeq_ambientSine` turns that into the norm identity; and `DavisKahan1970.norm_sinAngleOperatorC_lt_one_of_unboundedRitz` exposes the uniform transversality the tangent theorem's proof already derived inline, which is what both of the first two need. What remains is the scalar field alone. |
| **note** | `H₀ = 0` is carried twice, by `RitzData.residual_orthogonal` and by `D.residual = P_{Uᗮ}∘H∘ι_U`; this is the source's own double presentation in `(1.8)`. |

---

## 3. `S2-sin-two-theta` — two printed clauses

Shared source data: `A` self-adjoint, `U` reducing `A`, `SylvesterGap` between the two
blocks of `A`.

### 3.0 Where the unbounded compression stops, and why this row changed

The previous pass recorded "bounded `M` → partial compression" as an open
*production* obligation for this clause. That was wrong, and it put this audit in
direct contradiction with the production semantic audit of the same day, which
had concluded that the Appendix does not extend the double-angle sine theorem to
an unbounded trial compression. One of the two had to move; re-reading the source
says it is this one.

The Appendix to Section 6 enumerates which theorems get which relaxation:

> For the sine theorem, one of `A₀, Λ₁` may be unbounded. … Proposition 6.1 and
> Theorem 6.1 admit the analogous relaxation.
>
> For the tangent theorem the Appendix explicitly returns to the ordered
> hypotheses `A₀ ≤ α` and `Λ₁ ≥ α + δ` in the general case and allows *both* `A₀`
> and `Λ₁` to be unbounded.

Two things follow. The sine family gets "**one** of the two"; only the tangent
theorem gets "**both**". And **no double-angle result is named in the Appendix at
all** — not the `sin 2Θ` theorem, not the `tan 2Θ` theorem, not Theorem 7.1.

In the directed `sin 2Θ` configuration the two blocks are the trial compression
and the unwanted exact block, and the production endpoint has the exact allowed
shape: the ambient operator and the exact block may be unbounded, the trial
compression is bounded. That is "one of the two", so the printed scope is met.

Accordingly the Challenge now uses a distinct structure for this clause:

| structure | compression | used by |
| --- | --- | --- |
| `TrialBlock` / `RitzData` | `U →ₗ.[𝕜] U`, partial | `tan Θ`, where the Appendix asks for it |
| `BoundedTrialBlock` | `U →L[𝕜] U`, bounded | `sin 2Θ` directed |

Two residual narrowings are worth naming rather than hiding, because a hostile
reader will find them:

* `BoundedTrialBlock.mem_domain` puts all of the trial subspace inside `dom A`.
  This is not an extra restriction beyond what the printed `(1.8)` needs: with `A`
  closed self-adjoint and the trial subspace closed and inside `dom A`, the
  compression is automatically bounded by the closed graph theorem, so the
  bounded-compression and inside-the-domain hypotheses are the same hypothesis.
* Nothing here reopens the reducing-versus-spectral question; that is a separate
  row, and it is still open for this clause.

### 3a. directed — `δ‖sin 2Θ₀‖ ≤ 2‖R‖`

| | |
| --- | --- |
| **paper clause** | `δ‖sin(2Θ₀)‖ ≤ 2‖R‖` |
| **Challenge** | `SinTwoThetaResult.directed` |
| **production witness** | `sinTwoTheta_directed_unboundedResidual_blockRepresentative_reducing_paperUINorm_complex` / `…_real` |
| **correspondence** | **`Solution.sinTwoTheta_directed_proof` — proved** |
| **real/complex** | `[RCLike 𝕜]` ✓, by `TauCeti.ScalarTransport` from the two fixed-field endpoints |
| **bounded/unbounded** | `BoundedTrialBlock A V` — **bounded** compression `M : V →L[𝕜] V`, `V ≤ dom A`, bounded residual, matching production exactly. Narrowed from `TrialBlock` on 2026-09-01; see §3.0 |
| **dimension** | arbitrary ✓ |
| **norm** | `UINorm` ✓ |
| **gap** | full `SylvesterGap` on `block A U` / `block A Uᗮ` ✓ (production: the same predicate on the two **reducing** restrictions, since 2026-09-01) |
| **RHS quantity** | `2 * N.norm D.residual`, hypothesis `N.Finite D.residual` only ✓ |
| **angle multiplicity** | directed, once: `directedDoubleSine U V = P_U ∘ P_{J_V Uᗮ}` = production's `sinTwoThetaIdealBlock U V`, name for name ✓ |
| **constant** | `2` ✓ |
| **status** | **proved, at arbitrary `[RCLike 𝕜]`** (`Solution.sinTwoTheta_directed_proof`). Two obligations closed. The compression obligation is **withdrawn**: it was not a source obligation, and demanding it contradicted the production semantic audit (§3.0). The spectral-versus-reducing obligation is **discharged**, not deferred: `sinTwoTheta_reflectionResidual_block_gauge_of_formGap_reducing` and its real mirror state the base estimate at an arbitrary reducing subspace, because the three spectral ingredients each have a reducing analogue and the third is literal once the complement is `Uᗮ`. |

### 3b. ambient — `δ‖sin 2Θ‖ ≤ 2‖H‖`

| | |
| --- | --- |
| **paper clause** | `δ‖sin(2Θ)‖ ≤ 2‖H‖` |
| **Challenge** | `SinTwoThetaResult.ambient` |
| **production witness** | `sinTwoTheta_ambient_reflection_projectorDifference_paperUINorm` (scalar-generic), specialized by `sinTwoTheta_ambient_unbounded_addBounded_paperUINorm_complex` / `…_real` |
| **correspondence** | **`Solution.sinTwoTheta_ambient_proof` — proved**, with no capability binder |
| **real/complex** | `[RCLike 𝕜]` ✓ (the production theorem applied is itself scalar-generic) |
| **bounded/unbounded** | `A` a partial map, `H` bounded self-adjoint ✓ |
| **dimension** | arbitrary ✓ |
| **norm** | `UINorm` ✓ |
| **gap** | full `SylvesterGap` on the two blocks of `A`, at an **arbitrary reducing** `U` ✓ |
| **RHS quantity** | `2 * N.norm H`, hypothesis `N.Finite H` only ✓ |
| **angle multiplicity** | ambient, twice: `ambientDoubleSine U V = P_{J_V U} − P_U`, which is what `paperSinTwoAngleOperatorC_eq_modulus_starProjection_sub` identifies with the paper's `sin 2Θ` ✓ |
| **constant** | `2` ✓ |
| **status** | **exact and discharged.** This clause settles the reducing-versus-spectral question in the Challenge's favour for `sin 2Θ`: the development's ambient theorem already holds at arbitrary reducing `U`, and `Solution.reflectionIntertwines_of_reduces` supplies the reflection data from the source's own hypothesis that `Q` reduces `A + H`. |

---

## 4. `S2-tan-two-theta` — two printed clauses

Shared source data: `A` self-adjoint, `U` reducing `A` ordered below `α` with complement
above `α + δ`, `H` bounded self-adjoint with `H₀ = H₁ = 0`.

### 4a. directed — `δ‖tan 2Θ₀‖ ≤ 2‖R‖`

| | |
| --- | --- |
| **paper clause** | `δ‖tan(2Θ₀)‖ ≤ 2‖R‖`, no independent pole hypothesis |
| **Challenge** | `TanTwoThetaResult.directed` |
| **production witness** | `tanTwoTheta_directed_unboundedResidual_blockRepresentative_paperUINorm_complex` / `…_real` |
| **correspondence** | **not carried out** |
| **real/complex** | `[RCLike 𝕜]`; production fixed-field |
| **bounded/unbounded** | `A` a partial map, `H` bounded ✓ (production the same) |
| **dimension** | arbitrary ✓ |
| **norm** | `UINorm` ✓ |
| **gap** | ordered form bounds on `block A U` / `block A Uᗮ`; production fixes `U = specRange hA (Iic c)` — the same narrowing as 3a |
| **off-diagonal** | `P_U H P_U = 0` **and** `P_{Uᗮ} H P_{Uᗮ} = 0`; `Solution.isOddFor_of_offDiagonal` **proves** this is production's `IsOddFor U H` ✓ |
| **RHS quantity** | `2 * N.norm (P_{Uᗮ} H P_U)` with hypothesis `N.Finite (P_{Uᗮ} H P_U)` — the **corner**, not `H` ✓ (production requires membership of exactly the corner `paperBlockCompression Uᗮ U B`) |
| **angle multiplicity** | directed, once: `tanSeq (directedDoubleSine U V)`, `directedDoubleSine U V = P_U P_{J_V Uᗮ}`, whose singular values are `sin 2θⱼ` once. `hasSameApproximationNumbers_reflectionSineCorner_sinTwoThetaIdealBlock` proves the production corner `reflectionSineCorner U J_V` has that same sequence, and `approximationNumber_reflectionTangentCorner` turns it into `tan (arcsin ·)` ✓ |
| **constant** | `2` ✓ |
| **pole handling** | `TangentDefined (directedDoubleSine U V)` is a **conclusion**, matching production's `IsUnit (diagonalPart J · diagonalPart J)` conclusion and the source's “Section 7 derives the nonvanishing … rather than assuming it” ✓.  Read on the *doubled* sine it is the uniform `‖sin 2Θ₀‖ < 1`, not a sequence check on the single angle; see §6.1 |
| **status** | **proved, at arbitrary `[RCLike 𝕜]`** (`Solution.tanTwoTheta_directed_proof`). The multiplicity question this row was held open for is settled the other way round from the way it was posed: the doubled tangent is read off the *doubled* sine, and `hasSameApproximationNumbers_reflectionSineCorner_sinTwoThetaIdealBlock` proves the production corner carries exactly that sequence, each directed angle once. `sameApproximationSingularValues_unboundedReflectionTangent` — which concerns the **uncornered ambient** tangent and so carries doubled ambient multiplicity — is not used. |

### 4b. ambient — `δ‖tan 2Θ‖ ≤ 2‖H‖`

| | |
| --- | --- |
| **paper clause** | `δ‖tan(2Θ)‖ ≤ 2‖H‖` |
| **Challenge** | `TanTwoThetaResult.ambient` |
| **production witness** | `tanTwoTheta_ambient_unbounded_paperUINorm_complex` / `…_real` |
| **correspondence** | **not carried out** |
| **real/complex** | `[RCLike 𝕜]`; production fixed-field |
| **bounded/unbounded** | `A` a partial map, `H` bounded ✓ |
| **dimension** | arbitrary ✓ |
| **norm** | `UINorm` ✓ |
| **gap** | ordered form bounds; production fixes `U` spectrally (same narrowing) |
| **RHS quantity** | `2 * N.norm H`, hypothesis `N.Finite H` ✓ |
| **angle multiplicity** | ambient, with the ambient multiplicity: `tanSeq (ambientDoubleSine U V)`, `ambientDoubleSine U V = P_{J_V U} − P_U`. Production concludes on `paperAbsTanTwoAngleOperatorC U V`, and `approximationNumber_paperAbsTanTwoAngleOperatorC_projectorDifference` proves the two sequences agree ✓ |
| **constant** | `2` ✓ |
| **pole handling** | conclusion, as in 4a; production's docstring says explicitly that no pole hypothesis is asked of the caller ✓ |
| **status** | **proved, at arbitrary `[RCLike 𝕜]`** (`Solution.tanTwoTheta_ambient_proof`). |
| **note** | `V` is quantified inside each clause rather than shared, which is strictly stronger and matches “each clause quantifies its own data”. |

---

## 5. Defects this audit was built to catch, and their disposition

| # | defect | where found | disposition |
| --- | --- | --- | --- |
| 1 | tangent defined from the **residual**: the first draft's `tanTheta` said `∀ T, IsTangentOf R T → …`, taking `tan(arcsin sₙ(R))` — a different and false quantity | reviewer | **fixed.** `tanSeq` now takes a *sine*, and its docstring says so in a paragraph that names the mistake. `directedSineBlock`, `ambientSine`, `directedDoubleSine` and `ambientDoubleSine` are the only arguments used, and each is a sine. |
| 2 | bounded Ritz compression substituted for unbounded: `M : U →L[𝕜] U` | reviewer | **fixed, then bounded again where the source bounds it.** `TrialBlock.compression : U →ₗ.[𝕜] U` is a partial map and `RitzData` adds only the orthogonality; but the `sin 2Θ` directed clause uses `BoundedTrialBlock`, because the Appendix grants "both unbounded" to the tangent theorem alone. See §3.0. |
| 3 | ambient ideal membership imposed on the directed clause: `N.Finite H` in the common telescope of `tanTheta` and `tanTwoTheta` | reviewer | **fixed.** The three two-clause theorems now conclude in `TanThetaResult` / `SinTwoThetaResult` / `TanTwoThetaResult`, whose fields carry their own data and their own membership premise. The directed `tan 2Θ` premise is membership of the **corner**. |
| 4 | arbitrary reducing subspace substituted for spectral selection without proof | prior pass, self-found | **resolved in the Challenge's favour, and proved for `sin 2Θ` ambient.** Section 1 of the source assumes reduction, not spectral selection, so the reducing formulation is the printed one; the remaining spectral-only production endpoints are recorded above as *production* obligations, not Challenge defects. |
| 5 | tangent-witness vacuity: `∀ T, IsTangentOf S T → …` says nothing when no `T` exists | reviewer | **fixed.** `UINorm.evalSeq` measures the tangent sequence directly. `IsTangentOf` and `IsDoubleTangentOf` are deleted. |
| 6 | pole encoded as a harmless numerical zero (`Real.tan (π/2) = 0` in Lean) | reviewer | **fixed by the second permitted route:** `TangentDefined` is stated as a **conclusion**, so a pole is not silently valued at zero — the theorem asserts there is none. This matches the source (Section 7 derives it) and production (`IsUnit …` in the conclusion). |
| 7 | the printed lower bound `β` on `spec(A₀)` is dropped from the ordered-gap clauses (`tan Θ`, `tan 2Θ`) | this audit | **resolved as source-exact, 2026-09-01 — see §5.1.** The Appendix to Section 6 drops `β` itself. |
| 8 | `sinAngleOperatorC` is `modulus (P_U − P_V)` while the Challenge's `ambientSine` is `P_V − P_U` | this audit | **benign, and recorded.** Sign and modulus do not change singular values; every correspondence goes through approximation numbers, and `DavisKahan1970.approximationNumber_sinAngleOperatorC` now proves the equality outright. |
| 9 | the unbounded compression demanded of `sin 2Θ` directed, in contradiction with the production semantic audit of the same day | reviewer | **fixed.** `BoundedTrialBlock`; see §3.0 for the Appendix passage that decides it. |
| 10 | a tangent clause whose operator is only *claimed* to have the tangent singular values | this audit | **closed for the ambient single angle, sharpened for the doubled one.** `DavisKahan1970.approximationNumber_paperTanAngleOperatorC` and `…_paperAbsTanTwoAngleOperatorC` prove the identity from the Pythagorean operator relation alone, by pairing the Gram resolvent transfer with its inverse (`TauCeti.ApproximationNumber.approximationNumber_le_of_gramContraction`). |

#| 11 | the doubled tangent read off the **single**-angle sine, by applying the non-monotone `\|tan (2 arcsin ·)\|` index by index to `aₙ(sin Θ)` | reviewer | **fixed, 2026-09-01.** `θ ↦ sin 2θ` is not monotone on `[0, π/2]`; principal angles `75°` and `30°` order the two sequences oppositely. Both `tan 2Θ` clauses now read the doubled tangent off the double-angle sine through the monotone `u ↦ tan (arcsin u)`. See §6.1. |
| 12 | pole certificate that a noncompact operator's interior spectrum can evade: `DoubleTangentDefined` looked only at `aₙ(sin Θ)` | reviewer | **fixed, 2026-09-01.** The certificate is `TangentDefined` of the double-angle sine, whose `a₀` is `‖sin 2Θ‖`; that is the uniform quarter-turn exclusion production derives. |

## 5.1 The dropped `β`, resolved

The previous pass recorded the missing `β` as "strictly stronger, accepted", and
that was the wrong disposition: a statement is not *exact* while it also carries
an unexplained stronger variant.  The resolution is **Route A** — the β-free
spelling is the source's own, and the source says so.

The Section 2 tangent theorem is printed with a two-sided hypothesis:

> `spec(A₀) ⊂ [β,α]`,  `spec(Λ₁) ⊂ [α+δ,∞)`,  `δ > 0`.

The Appendix to Section 6 then returns to the same theorem in the general case
and states its hypotheses without `β`:

> For the tangent theorem the Appendix explicitly returns to the ordered
> hypotheses `A₀ ≤ α` and `Λ₁ ≥ α + δ` in the general case and allows *both*
> `A₀` and `Λ₁` to be unbounded; the residual entering the displayed norm
> estimate is still required to be bounded.

`A₀ ≤ α` is a form bound with no lower end, and it is asserted *of the tangent
theorem*, not of some other result.  A lower bound `β` would contradict the
sentence it appears in: an operator confined to `[β,α]` is bounded, and the
Appendix is saying `A₀` need not be.  So the β-free ordered hypothesis is the
scope the source claims for this theorem, and the finite-interval spelling in
Section 2 is the special case the main exposition works in.

Three consequences, recorded so this is checkable rather than asserted:

| | |
|---|---|
| printed finite-interval spelling | `spec(A₀) ⊂ [β,α]`, `spec(Λ₁) ⊂ [α+δ,∞)` |
| half-infinite source extension | `A₀ ≤ α`, `Λ₁ ≥ α+δ`, both possibly unbounded (Appendix to Section 6) |
| Challenge spelling | `SemiboundedAbove D.compression α`, `SemiboundedBelow (block A Vᗮ …) (α+δ)` |
| relation | the Challenge spelling **is** the Appendix spelling; it implies the printed one by `spec(A₀) ⊂ [β,α] → A₀ ≤ α` |

The `tan Θ` rows above are therefore **EXACT at the paper's full scope**, not
"Lean strictly stronger".  The same argument covers `tan 2Θ`, whose printed
ordered hypothesis `spec(A₀) ⊂ [β,α]`, `spec(A₁) ⊂ [α+δ,∞)` the Challenge states
as the two form bounds; there the source's own `S2-unbounded-scope` sentence
("The spectral intervals in the gap hypotheses may be half-infinite") does the
same work without needing the Appendix.

This is also the disposition the production endpoints take, and as of 2026-08-31
the production certificate checks it: the source atom
`DK-6-appendix.unbounded-tangent-extension` now requires the witness to carry an
`UnboundedRitzPair`, whose compression is a partial map, and forbids the
bounded-compression trial block.

## 6. What the audit does not certify

It certifies that each Challenge clause *states* the printed clause at the printed scope.
It does not certify that the Challenge theorems are true — four are `sorry`-bodied by the
Comparator convention — and it does not certify the correspondences marked *open*.

**Clause scoreboard, 2026-09-01.**

| clause | correspondence |
| --- | --- |
| `sin Θ` | **proved, arbitrary `[RCLike 𝕜]`** (`Solution.sinTheta_proof`) |
| `tan Θ` directed | **proved, arbitrary `[RCLike 𝕜]`** (`Solution.tanTheta_directed_proof`) |
| `tan Θ` ambient | **proved, arbitrary `[RCLike 𝕜]`** (`Solution.tanTheta_ambient_proof`) |
| `sin 2Θ` directed | **proved, arbitrary `[RCLike 𝕜]`** (`Solution.sinTwoTheta_directed_proof`) |
| `sin 2Θ` ambient | **proved, arbitrary `[RCLike 𝕜]`** (`Solution.sinTwoTheta_ambient_proof`) |
| `tan 2Θ` directed | **proved, arbitrary `[RCLike 𝕜]`** (`Solution.tanTwoTheta_directed_proof`) |
| `tan 2Θ` ambient | **proved, arbitrary `[RCLike 𝕜]`** (`Solution.tanTwoTheta_ambient_proof`) |

All seven printed inequality clauses are proved at the Challenge's own scalar scope.
None of the seven carries a capability binder, a field-dispatch hypothesis, a
finite-dimensionality hypothesis, or a spectral selection of the trial subspace.
`Solution.sinTheta_solution`, `tanTheta_solution`, `sinTwoTheta_solution` and
`tanTwoTheta_solution` assemble them into the Challenge's four statements; each
depends on `propext`, `Classical.choice`, `Quot.sound` and nothing else.

**How the scalar field was closed.**  Not by making the machinery generic —
`gramOperator`, `cfc` and the double-angle functional calculus are complex — but by
transport.  Every quantity a Challenge clause mentions is a function of one
operator's singular-value sequence, and `TauCeti.ScalarTransport` renames the field
without touching the vectors, the norm, the operators, or that sequence.
`RCLike.I_eq_zero_or_im_I_eq_one` supplies the case split, and the two fixed-field
proofs supply the content.  The real branch of each `tan` clause is itself proved by
complexification, so the mathematics happens once, over `ℂ`.

**What this audit still does not certify.**  It does not certify that the Challenge
theorems are true — four are `sorry`-bodied by the Comparator convention, and the
proofs live in `Solution.lean`.  It certifies that each Challenge clause *states* the
printed clause at the printed scope, and it now records, clause by clause, the
`Solution` declaration that discharges it.

### 6.1 The identity that is false, and must not be retried

An earlier pass named the remaining `tan 2Θ` obligation as

```text
aₙ(sin 2Θ) = sin (2 arcsin aₙ(sin Θ)).
```

**That identity is false in general.**  `θ ↦ sin 2θ` is not monotone on `[0, π/2]`,
so applying it index by index to an ordered singular-value sequence need not give an
ordered sequence.  Principal angles `75°` and `30°` already break it:

```text
sin 75° > sin 30°     while     sin 150° = 1/2 < √3/2 = sin 60°.
```

The transformed sequence is in the opposite order from `aₙ(sin 2Θ)`, so no indexwise
theorem of that shape exists without an acute restriction the source does not impose.

The `tan 2Θ` clauses accordingly read the doubled tangent off the **double-angle
sine** — `directedDoubleSine`, `ambientDoubleSine` — through the *monotone*
`u ↦ tan (arcsin u)`, which is `|tan 2θ| = tan (arcsin |sin 2θ|)` and needs no branch
choice.  `absTanTwoSeq`, `DoubleTangentDefined` and `directedSineCorner` are gone from
the Challenge; the pole certificate is `TangentDefined` of the double-angle sine,
which at `a₀ = ‖·‖` is the uniform quarter-turn exclusion `‖sin 2Θ‖ < 1` rather than a
sequence-only check that an interior spectral value of a noncompact operator can evade.

### 6.2 What `TangentDefined` is, and is not

`TangentDefined S` is **not** an eighth printed inequality clause.  It is a derived
semantic/domain certificate, made explicit because Lean's `Real.tan` is total and
therefore assigns a value at a pole where the paper's `tan Θ` has none.  Davis and
Kahan derive the corresponding non-vanishing rather than assuming it, so it appears
in the Challenge as a *conclusion*.  The audit counts **seven printed inequality
clauses**; `TangentDefined` and the singular-value correspondences beneath it are the
derived domain facts needed to formalize the paper's notation, not additional
printed content.

