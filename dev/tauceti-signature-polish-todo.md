# Tau Ceti Signature and API Polish Backlog

*Declaration-level TODOs for adversarial review readiness*

**Audit baseline**
DKPS archive: 543b46f42573 (24 July 2026)
Scope: staged ForTauCeti declarations plus next-wave convergence APIs
Purpose: design review only; no signatures are changed by this document

> **How to use this document**
>
> Treat every proposed Lean signature as a review sketch, not a compile-ready patch. The backlog distinguishes cosmetic naming work from semantic API decisions. P0 items must be settled before a roadmap or code PR; P1 items should be resolved before review; P2 items complete the characteristic API; P3 items are cleanup or optional generalizations.

## Contents

1. Executive assessment

2. Adversarial review model

3. Global signature rules

4. Priority and PR slicing

5. Approximation-number foundation

6. ~~Courant-Fischer and finite spectral API~~ — RESOLVED, removed from backlog

7. ~~Operator modulus and absolute value convergence~~ — RESOLVED, removed from backlog

8. Inner-product-space utilities

9. ~~C*-algebra and matrix helpers~~ — RESOLVED, removed from backlog

10. ~~Measure-theory helpers~~ — RESOLVED, removed from backlog

11. ~~Haagerup-Zsido kernel decomposition~~ — RESOLVED, removed from backlog

12. Next-wave convergence signatures

13. Definition-level deletion and adapter plan

14. Pre-PR declaration checklist

1. Appendix A. Name-change index

1. Appendix B. Review questions to answer in roadmaps

## 1. Executive assessment

The staged library is mathematically substantial, but it is not yet a single Tau Ceti-native API. The dominant risk is not proof correctness. It is that independent local abstractions, donor abstractions from Spectra, and existing Tau Ceti structures encode the same mathematics in incompatible ways. A reviewer can correctly block direct duplication and can request changes for parallel APIs even when every theorem compiles.

> **Central recommendation**
>
> Do not run a blanket rename pass. First decide the canonical mathematical object and namespace, then redesign signatures around that object, then rename the surviving declarations. Renaming a parallel abstraction only makes the duplication harder to remove.

| **Cluster** | **Current state** | **Signature risk** | **Upstream action** | **Priority** |
| --- | --- | --- | --- | --- |
| Approximation numbers | Staged and Mathlib-only | ~~Codomain~~ (settled: ℝ); indexing pinned; characteristic API still P1 | Split into small PRs | P1 |
| Courant-Fischer | Staged helper layer | Misleading specSubspace and missing min-max endpoint | Refactor around basis spans and actual min-max theorem | P0 |
| Operator modulus / operatorAbs | Two overlapping APIs | Duplicate definitions and noncanonical names | Unify into one modulus API | P0 |
| Near isometry | Staged real finite-dimensional result | Existential instead of canonical polar factor; wrong generality split | ~~Define canonical object; derive finite equiv~~ **RESOLVED 2026-07-27** (§8.2): canonical `ContinuousLinearMap.polarIsometry` over arbitrary complex Hilbert spaces, sharp constant `δ`, real finite-dimensional statement returns the polar factorization | ~~P0~~ |
| Centered scatter | Staged | Custom finite mean and append family | Refactor to Finset/Fintype and reuse average/cons | P1 |
| Orthogonal series | Staged | Likely duplicate helpers; proof-shaped names | Reuse Orthogonal predicate and existing summability API | P1 |
| Haagerup-Zsido kernel | Staged monolith, 1673 lines | File size, public helper explosion, generic lemmas mixed in | Split into 7-8 modules; privatize/move helpers | P0 |
| Closed operators / semigroups | Production local API | Parallel to Tau Ceti LinearPMap architecture | Rewrite over LinearPMap properties | P0 |
| Symmetric ideal families | Production local structure | Unconstrained gauge off carrier; fixed universes | ~~Redesign as normed subtype/family~~ **RESOLVED 2026-07-27** (§12.1): single `ℝ≥0∞` gauge, carrier derived, adjoint layer split off | ~~P0~~ |
| Spectra spectral calculus | Vendored donor dependency | Needs provenance-preserving canonical port | Port minimal dependency-closed slices | P1 |

### What “Mathlib quality” means here

- The theorem name describes the conclusion, not the proof route or historical motivation.

- The signature sits at the natural level: weakest useful assumptions, no gratuitous parameters, no duplicated special case when a general theorem is available.

- A definition has a complete characteristic API, so downstream proofs do not unfold it.

- Public declarations are genuinely reusable; proof scaffolding stays private.

- The namespace and file are the canonical home for the object being extended.

- Existing Mathlib and Tau Ceti constructions are reused even when the local proof is already complete.

- Parallel APIs are collapsed before submission, especially for unbounded operators, moduli, Hilbert-Schmidt operators, and polar decomposition.

## 2. Adversarial review model

Tau Ceti review is deliberately multi-angle. The current review specification checks correctness, reuse, scope, attribution, API design, generality, placement, naming, documentation, and proof quality after mechanical CI is green. Reuse can block a PR when an existing declaration directly replaces a new one. Naming and API design are fixable but systematic sources of request-changes verdicts.

> **Review consequence**
>
> Every declaration in an upstream PR should arrive with an explicit answer to four questions: Why is this not already in Mathlib or Tau Ceti? Why is this the natural generality? Why is this the canonical namespace and file? What is the minimal characteristic API that lets consumers avoid unfolding it?

### Expected reviewer attack surface

| **Cluster** | **Current state** | **Signature risk** | **Upstream action** | **Priority** |
| --- | --- | --- | --- | --- |
| Correctness | Definition convention differs from literature; name overstates result | Specify indexing and semantics in roadmap and docstring | P0 |  |
| Reuse | Local helper duplicates existing theorem or combinator | Attach grep evidence and replacement plan | P0 |  |
| API design | Definition body exposed; missing iff/ext/apply API | Hide body; add characteristic lemmas | P1 |  |
| Generality | Real-only or finite-dimensional theorem without reason | Prove natural general form first or document obstruction | P1 |  |
| Placement | Generic theorem lives in roadmap-specific namespace/file | Move to canonical Mathlib/Tau Ceti topic | P1 |  |
| Naming | Name describes construction/proof or wrong quantifier | Rename from conclusion outward | P1 |  |
| Documentation | Docstring omits indexing, normalization, or donor provenance | State conventions and semantic differences precisely | P1 |  |
| Proof quality | Long plumbing proof recreates standard API | Search and fold around named lemmas | P2 |  |

## 3. Global signature rules

### 3.1 Settle representation before names

Decide the object type, indexing convention, scalar field, and universe policy before polishing declaration names. In particular, settle whether approximation numbers are NNReal-valued and zero-based; whether modulus is a ContinuousLinearMap method; and whether operator ideals are normed subtypes rather than a Mem/gauge record.

### 3.2 Name from the conclusion outward

Avoid names such as lowerBound_le_..., exists_... when the conclusion has a more direct standard description, or names that begin with the proof device. Quantifiers in the name must agree with the statement; forall_unit_vector_eigenvalue_le_re_inner currently begins with forall although its outer conclusion is existential.

### 3.3 Prefer canonical objects over existential wrappers

When the witness is canonical and choice-free, define it and provide apply/ext/simp lemmas. The near-isometry unitary should probably be the polar factor, not an anonymous W. The inverse in a C*-algebra should be a⁻¹ after proving IsUnit, not an existential j with two equations.

### 3.4 Avoid raw constructor noise in public conclusions

A public equality should not force users to read NNReal constructors such as ⟨singularValues n, nonneg⟩. Add a canonical NNReal singular-value accessor or state a coerced real equality.

### 3.5 Do not expose implementation bodies globally

The blanket @[expose] public section is a likely API-design finding. Keep bodies hidden and expose computation or characterization lemmas. A reviewer will prefer one precise _def theorem to downstream reliance on definitional equality.

### 3.6 Use structures and predicates already owned by Tau Ceti

Closed operators should be LinearPMap plus closedness/self-adjointness properties; semigroup generators already use LinearPMap. Do not upstream a second closed-operator universe because the downstream paper uses it.

### 3.7 Separate generic helpers from campaign-specific modules

A generic even-function integrability lemma does not belong in a Haagerup-Zsido kernel file. A cardinal universe helper does not belong in approximation numbers unless it remains private. Move general results to the earliest canonical home.

### 3.8 Make normalization explicit

State whether scatter is normalized, whether Fourier transform uses 2π, whether singular values are zero-padded, whether approximation numbers use rank ≤ n, and whether operator angles are directed or symmetric.

## 4. Priority and PR slicing

> **P0 means “do not submit yet”**
>
> A P0 item changes the mathematical public interface or removes a duplicate abstraction. P1 is required signature/name polish. P2 completes useful API or automation. P3 is optional cleanup. A PR should not mix P0 convergence refactors with downstream theorem additions.

1. PR A0: roadmap and representation decisions for approximation numbers and operator modulus.

1. PR A1: approximation-number Basic only, after convention and characteristic API are settled.

1. PR A2: adjoint invariance and finite-dimensional singular-value identification.

1. PR A3: min-max lower bound and Courant-Fischer support, preferably ending in an actual min-max theorem.

1. PR A4: one canonical operator modulus, deleting the parallel operatorAbs API downstream.

1. PR U1: **ACTIVE / CLAIMED.** LinearPMap convergence refactor for closed/self-adjoint operators; no new perturbation theorem. This is required representation work, not optional polish.

1. PR S1+: dependency-closed Spectra ports with exact provenance, after reuse audit.

1. Independent utility PRs: centered scatter, orthogonal series, measure-theory criteria, only if roadmapped and reuse-clean.

1. Haagerup-Zsido series: split prerequisite analytic lemmas from the final kernel theorem; no 1673-line PR.

## 5. Approximation-number foundation

> **RECONCILED 2026-07-27 — §5.1 and §5.4 are closed; §5.2 and §5.3 are what is left.**
> The audit that used to sit here recorded a divergence between this section and the tree;
> that divergence has been worked off item by item against
> `ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/`, and every §5.1 heading is now
> struck through with its disposition and the reasoning that settled it.
>
> - **§5.1 Basic.lean — CLOSED.** The one genuinely-open P0,
>   `rank_comp_left_le_of_rank_le`, could not be privatized (four independent consumers), so
>   it was moved out and generalized to `LinearMap.rank_comp_le_natCast_right` in
>   `ForTauCeti/LinearAlgebra/Dimension/RankComp.lean`; `Basic.lean` now carries
>   approximation-number API and nothing else. Seven renames landed, three items were
>   verified-and-kept with the reason recorded, and two blocks were stale text rather than
>   work. Name index in Appendix A.
> - **§5.4 MinMax.lean — CLOSED** earlier the same day; see the lane note in `dev/LANES.md`.
> - **§5.2 Adjoint.lean and §5.3 FiniteDimensional.lean — still open**, and still to be
>   re-checked against the tree before being worked: the same drift that produced this audit
>   block applies to them. Known specifics: §5.3's `singularValues_le_norm_sub_of_rank_le`,
>   `singularValues_le_approximationNumber` and `approximationNumber_eq_singularValues` are
>   already struck through, so what remains there is `approximationNumber_le_singularValues`;
>   §5.2 carries a single P1 "keep or annotate".


### 5.1 Basic.lean

| **Current file** | ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean |
| --- | --- |
| **Proposed disposition** | Keep the mathematics; redesign the convention/API before upstreaming. |
| **Readiness** | Medium. Proofs are mature, but the representation decision affects every later theorem. |
| **Primary review risks** | Zero-based rank convention; NNReal versus Real; global namespace extension; overexposed body; vague characteristic theorem names. |
| **Likely PR slice** | PR A1 after roadmap acceptance. |

> **P0 convention decision — RESOLVED 2026-07-27: zero-based**
>
> `aₙ(T) = dist(T, {rank ≤ n})`, so `a₀(T) = ‖T‖`; the one-based literature `s`-numbers are `sₙ = a_{n-1}`. Approved as decision 1 of `ForTauCetiRoadmap/ApproximationNumbers/README.md`, with the reviewer-facing argument recorded there and summarized in a new "The index convention" section of the module docstring. Decisive point: Mathlib's `LinearMap.singularValues` is **zero**-indexed, so the flagship identification is the index-free `aₙ(T) = σₙ(T)`; one-based numbering would make it `sₙ(T) = σ_{n-1}(T)`, putting *truncated* `ℕ`-subtraction (and an `n ≠ 0` side condition) into the headline theorem. Same for every ideal inequality (`a_{m+n} ≤ aₘ + aₙ` vs `s_{m+n-1}`), and `a₀ = ‖T‖` is a theorem rather than a definition-by-fiat over an empty infimum. Deliberately **not** done: no one-based `sNumber` definition and no bridge theorem — a bridge needs something to bridge to, and adding it would reintroduce the duplicate API the "do not carry both" rule (decision 2) exists to prevent. The translation is documented instead.

> **P0 codomain decision — RESOLVED 2026-07-24: `ℝ`**
>
> `ContinuousLinearMap.approximationNumber : ℝ` plus `approximationNumber_nonneg`, with no `ℝ≥0` API at all (not even an accessor). Deciding precedent: `Metric.infDist` — an infimum of nonnegative reals — is real-valued in Mathlib, as are `norm`, `dist`, and `singularValues`. The `ℝ≥0` codomain was paying a tax at both boundaries: `⟨value, proof⟩` constructor noise in the flagship Eckart–Young statements, and a real-valued `approximationSingularValue` wrapper downstream. Executed across the workspace; two NNReal↔ℝ bridging layers were deleted outright. Full rationale in `ForTauCetiRoadmap/ApproximationNumbers/README.md` decision 2.

#### P0  ~~le_natCast_of_lift_le~~ — RESOLVED 2026-07-27

**Disposition: Moved and generalized to an iff.**  Now
`Cardinal.lift_le_natCast : Cardinal.lift.{w} c ≤ ↑n ↔ c ≤ ↑n` in its own
dependency-closed module `ForTauCeti/SetTheory/Cardinal/Lift.lean`, separately
upstreamable to `Mathlib/SetTheory/Cardinal/Order.lean`, so the operator-ideal
PR carries no `Cardinal` namespace extension.  **Reuse audit run as requested:**
Mathlib has the two ingredients (`Cardinal.lift_natCast`, `Cardinal.lift_le`)
and the analogous cancellations for the `ℵ`/`ℶ`/`ω` families
(`aleph_natCast_le_lift`, `beth_natCast_le_lift`, `omega_natCast_le_lift`) — the
iff shape is copied from those — but not this statement, so it is not a
duplicate.  **Privatizing was not an option** (the review's first alternative):
it has four call sites across three ForTauCeti modules plus one `DavisKahan`
consumer.  The four call sites are now `Cardinal.lift_le_natCast.mp`.
Gotcha for whoever upstreams it: the two `↑n`s live in *different* universes
(`Cardinal.{max v w}` and `Cardinal.{v}`), so both need explicit universe
ascriptions in the statement, and the proof must rewrite under `conv_lhs` — a
bare `rw [← lift_natCast]` unifies the two sides and fails.

*Original disposition:*

**Disposition: Privatize or move**

```lean
theorem le_natCast_of_lift_le {c : Cardinal.{v}} {n : ℕ} (h : Cardinal.lift.{w} c ≤ (n : Cardinal)) : c ≤ (n : Cardinal)
```

**Proposed target shape**

```lean
private theorem rank_le_natCast_of_lift_rank_le
    {c : Cardinal.{v}} {n : ℕ}
    (h : Cardinal.lift.{w} c ≤ n) : c ≤ n
```

- Search Mathlib again for a lift cancellation theorem before retaining this helper.

- If only approximation-number proofs use it, keep it private in the first file that needs it.

- Do not extend namespace Cardinal publicly without an independent, broadly useful API case.

**Likely adversarial review:** A generic global Cardinal theorem in an operator-ideal PR will be challenged for placement and reuse.

#### P0  ~~approximationNumber~~ — RESOLVED (stale text, reconciled 2026-07-27)

**Disposition: Nothing was open here.**  Both questions this block asks had
already been answered by the two decision callouts above it, and the code has
read `ContinuousLinearMap.approximationNumber (T : E →L[𝕜] F) (n : ℕ) : ℝ`
since the codomain decision landed (`Basic.lean:134`).  The sketch below still
shows `ℝ≥0` and an "undecided convention"; that is a documentation lag, not
work.  Of its four bullets, three are done — dot notation retained and
justified in the module's "Namespace note", the zero-based convention stated in
the first sentence of both the definition docstring and the module overview,
and the body no longer needs unfolding now that
`approximationNumber_le_norm_sub` / `le_approximationNumber_iff` /
`approximationNumber_eq_iInf` cover it.  The fourth, an internal
`rankAtMost n R` abbreviation "to reduce repeated `Cardinal` casts", was
**deliberately declined**: the cast appears in exactly one place per statement,
and a private predicate would put a Tau Ceti-owned name into the *hypothesis*
of every public theorem, which is a worse trade than a visible `(n : Cardinal)`.

*Original disposition:*

**Disposition: Representation decision**

```lean
noncomputable def approximationNumber (T : E →L[𝕜] F) (n : ℕ) : ℝ≥0
```

**Proposed target shape**

```lean
noncomputable def ContinuousLinearMap.approximationNumber
    (T : E →L[𝕜] F) (n : ℕ) : ℝ≥0
-- chosen convention: infimum over R with R.rank ≤ n
```

- Retain dot notation only if Tau Ceti accepts extending ContinuousLinearMap.

- Put the zero-based convention in the first sentence of the docstring and module overview.

- Consider an internal predicate rankAtMost n R to reduce repeated Cardinal casts.

- Hide the definition body; consumers should use characterization lemmas.

**Likely adversarial review:** The reviewer may regard an unannounced nonstandard index convention as a correctness/API defect.

#### P1  ~~approximationNumber_def~~ — RESOLVED 2026-07-27

**Disposition: Renamed to `approximationNumber_eq_iInf` and de-simped.**  The
`@[simp]` attribute is gone (a `ciInf` over a subtype is not a normal form for a
norm-like quantity) and the docstring points readers at
`approximationNumber_le_norm_sub` / `le_approximationNumber_iff` instead.  Three
internal proofs that had been relying on it as a `simp` lemma now name it
explicitly.  Note the `@[expose] public section` question raised alongside this
item in roadmap item 8 is *not* settled here: dropping the blanket `@[expose]`
is a module-system change and belongs to the deferred repo-wide module-system
pass, not to a single file.

*Original disposition:*

**Disposition: Rename and de-simp**

```lean
theorem approximationNumber_def (T : E →L[𝕜] F) (n : ℕ) : T.approximationNumber n = ⨅ R : {R : E →L[𝕜] F // R.rank ≤ (n : Cardinal)}, ‖T - R.1‖₊
```

**Proposed target shape**

```lean
theorem approximationNumber_eq_iInf (T : E →L[𝕜] F) (n : ℕ) :
    T.approximationNumber n =
      ⨅ R : {R : E →L[𝕜] F // R.rank ≤ n}, ‖T - R‖₊
```

- Rename to describe the right-hand side rather than merely _def.

- Remove @[simp]; unfolding an infimum is not a stable simplifier normal form.

- Use this as an explicit theorem for proofs that need the implementation.

**Likely adversarial review:** An @[simp] theorem that expands a high-level invariant into ciInf is a likely API-design request change.

#### P1  ~~approximationNumber_le~~ — RESOLVED 2026-07-27

**Disposition: Renamed to `approximationNumber_le_norm_sub`** (conclusion-describing
suffix, as asked).  Ten call sites repointed across `ForTauCeti` and `DavisKahan`.

*Original disposition:*

**Disposition: Rename**

```lean
theorem approximationNumber_le (T : E →L[𝕜] F) {n : ℕ} {R : E →L[𝕜] F} (hR : R.rank ≤ (n : Cardinal)) : T.approximationNumber n ≤ ‖T - R‖₊
```

**Proposed target shape**

```lean
theorem approximationNumber_le_nnnorm_sub
    (T : E →L[𝕜] F) (hR : R.rank ≤ n) :
    T.approximationNumber n ≤ ‖T - R‖₊
```

- Make R and n explicit enough for discoverability; retain dot notation if desired.

- Use a conclusion-describing suffix; approximationNumber_le alone is too weak to search.

- Pair it with a lower-bound iff characterization.

**Likely adversarial review:** The current name omits the actual upper bound and forces users to inspect the signature.

#### P1  ~~le_approximationNumber~~ — RESOLVED 2026-07-27

**Disposition: Replaced by the iff `le_approximationNumber_iff`.**  The old
introduction rule is `…​.mpr`; per the review's "keep only one public theorem"
rule no named wrapper was retained, and the four call sites now use `.mpr`
directly.  `x` became implicit (it is determined by the goal in every use).

*Original disposition:*

**Disposition: Strengthen API**

```lean
theorem le_approximationNumber (T : E →L[𝕜] F) {n : ℕ} (x : ℝ≥0) (h : ∀ R : E →L[𝕜] F, R.rank ≤ (n : Cardinal) → x ≤ ‖T - R‖₊) : x ≤ T.approximationNumber n
```

**Proposed target shape**

```lean
theorem le_approximationNumber_iff :
    x ≤ T.approximationNumber n ↔
      ∀ R, R.rank ≤ n → x ≤ ‖T - R‖₊
```

- Prefer an iff characteristic theorem; derive the current introduction rule as .2 if a named wrapper is still useful.

- Keep only one public theorem unless both directions have independent consumers.

- If codomain changes to ℝ, state x : ℝ and let nonneg be separate.

**Likely adversarial review:** The current one-way introduction rule leaves the definition without a complete elimination/characterization API.

#### P1  ~~approximationNumber_eq~~ — RESOLVED 2026-07-27

**Disposition: Renamed to `approximationNumber_eq_norm_sub_of_forall_le`.**  The
generic `_eq` is gone, as asked, and the name now says why equality holds.  The
review's alternative — phrase the minimality hypothesis as `IsLeast` over the
set of admissible distances — was **considered and declined**: it would force
every call site to build `{x | ∃ S, S.rank ≤ n ∧ x = ‖T - S‖}` and then destructure
it, where the explicit `∀ S` form is applied directly.  The theorem had zero
external consumers, so the rename cost nothing; it is kept public because it is
the statement an Eckart–Young-style argument actually cites.

*Original disposition:*

**Disposition: Rename**

```lean
theorem approximationNumber_eq (T : E →L[𝕜] F) {n : ℕ} {R : E →L[𝕜] F} (hR : R.rank ≤ (n : Cardinal)) (hbest : ∀ S : E →L[𝕜] F, S.rank ≤ (n : Cardinal) → ‖T - R‖₊ ≤ ‖T - S‖₊) : T.approximationNumber n = ‖T - R‖₊
```

**Proposed target shape**

```lean
theorem approximationNumber_eq_nnnorm_sub_of_isLeast
    (hR : R.rank ≤ n)
    (hmin : ∀ S, S.rank ≤ n → ‖T - R‖₊ ≤ ‖T - S‖₊) :
    T.approximationNumber n = ‖T - R‖₊
```

- Rename the theorem to state why equality holds.

- Consider expressing hmin as IsLeast over the set of admissible distances.

- Avoid a generic _eq name in a namespace that will accumulate many equality theorems.

**Likely adversarial review:** The name approximationNumber_eq is not searchable and will collide conceptually with later equality characterizations.

#### P1  ~~approximationNumber_zero~~ — RESOLVED 2026-07-27

**Disposition: Renamed to `approximationNumber_index_zero`; the name
`approximationNumber_zero` now belongs to the zero *operator*.**  The review
asked for the docstring to say "zeroth, not first" — it does — but the deeper
problem was that two different theorems were competing for one name, and the
tree had assigned it to the *index*.  Mathlib's decisive precedent is the sibling
object: `LinearMap.singularValues_zero` is about the zero map, as are
`ContinuousLinearMap.opNorm_zero` and `LinearMap.rank_zero`; a head symbol
applied to `0` takes the plain `_zero` suffix.  Since this development's flagship
theorem is `approximationNumber_eq_singularValues`, having
`approximationNumber_zero` and `singularValues_zero` mean *different* things
would have been a genuine trap.  For the index Mathlib names the parameter's
role rather than its position (`eLpNorm_exponent_zero`), hence
`approximationNumber_index_zero`.  Both docstrings now point at each other.

*Original disposition:*

**Disposition: Keep with documentation**

```lean
theorem approximationNumber_zero (T : E →L[𝕜] F) : T.approximationNumber 0 = ‖T‖₊
```

**Proposed target shape**

```lean
@[simp] theorem approximationNumber_zero (T : E →L[𝕜] F) :
    T.approximationNumber 0 = ‖T‖₊
```

- Name and simp attribute are good if zero-based indexing is retained.

- Add the real-coercion version only if it is repeatedly needed; do not duplicate the theorem for both codomains.

- Docstring must call this the zeroth approximation number, not the first without qualification.

**Likely adversarial review:** The theorem is fine, but its semantics become misleading if the indexing convention is not prominently fixed.

#### P2  ~~antitone_approximationNumber~~ — RESOLVED 2026-07-27

**Disposition: Renamed to `approximationNumber_antitone`.**  The item asks to
"check adjacent Mathlib convention between `antitone_foo` and `foo_antitone`;
keep the locally consistent form" — the adjacent convention is
`LinearMap.singularValues_antitone`, on the object this one is proved equal to,
so the head symbol comes first.  It also makes `T.approximationNumber_antitone`
available by dot notation, which `antitone_approximationNumber` did not.
`@[gcongr]` was **not** added: the item makes it conditional on testing, and
`gcongr` wants a pointwise `≤`-to-`≤` lemma, not an `Antitone` bundle, so
tagging this would have done nothing.  No pointwise corollary was added either —
`approximationNumber_le_norm` is the only consumer and it uses the bundle.

*Original disposition:*

**Disposition: Keep / minor polish**

```lean
theorem antitone_approximationNumber (T : E →L[𝕜] F) : Antitone T.approximationNumber
```

**Proposed target shape**

```lean
theorem antitone_approximationNumber (T : E →L[𝕜] F) :
    Antitone T.approximationNumber
```

- Check adjacent Mathlib convention between antitone_foo and foo_antitone; keep the locally consistent form.

- Add the pointwise corollary only if consumers repeatedly need it.

- Mark with @[gcongr] only after testing that it helps and does not overfire.

**Likely adversarial review:** This is likely acceptable; the main review question is naming consistency with nearby Mathlib sequence APIs.

#### P2  ~~approximationNumber_le_nnnorm~~ — RESOLVED (renamed with the codomain decision)

**Disposition: Landed as `approximationNumber_le_norm`** (`Basic.lean:197`),
which is exactly the item's own conditional — "if the invariant becomes
real-valued, rename the bound to `approximationNumber_le_norm`".  It is derived
by antitonicity from `approximationNumber_index_zero`, the second of the two
routes the item offers.

*Original disposition:*

**Disposition: Keep**

```lean
theorem approximationNumber_le_nnnorm (T : E →L[𝕜] F) (n : ℕ) : T.approximationNumber n ≤ ‖T‖₊
```

**Proposed target shape**

```lean
theorem approximationNumber_le_nnnorm (T : E →L[𝕜] F) (n : ℕ) :
    T.approximationNumber n ≤ ‖T‖₊
```

- Keep if NNReal-valued.

- If the invariant becomes real-valued, rename the bound to approximationNumber_le_norm.

- Consider deriving by the zero approximant directly or antitonicity; current theorem is useful.

**Likely adversarial review:** Low risk, except the suffix must match the chosen codomain.

#### P2  ~~zero_approximationNumber~~ — RESOLVED 2026-07-27

**Disposition: Renamed to `approximationNumber_zero`** (not the sketched
`approximationNumber_zero_map`).  The item's own instruction was to check
Mathlib precedent, and precedent is unanimous that the head symbol leads:
`singularValues_zero`, `opNorm_zero`, `rank_zero`.  `_map` is not a Mathlib
suffix.  The name was free because the index statement moved to
`approximationNumber_index_zero` in the same pass — see that item for why the
swap, rather than a suffix on this one, is the right direction.  Exactly one
simp-normal name each, no aliases.

*Original disposition:*

**Disposition: Naming check**

```lean
theorem zero_approximationNumber (n : ℕ) : (0 : E →L[𝕜] F).approximationNumber n = 0
```

**Proposed target shape**

```lean
@[simp] theorem approximationNumber_zero_map (n : ℕ) :
    (0 : E →L[𝕜] F).approximationNumber n = 0
```

- Check Mathlib naming precedent: zero_approximationNumber may be correct for a function whose first argument is the map.

- Keep exactly one simp-normal-form name; do not add aliases.

- Ensure simplifier orientation reduces the invariant of zero.

**Likely adversarial review:** This is a naming consistency question rather than a semantic risk.

#### P1  ~~approximationNumber_nonneg~~ — RESOLVED: kept

**Disposition: Kept, unconditionally.**  The item is conditional on the codomain
and the codomain decision resolved to `ℝ`, which is the branch under which the
item itself says "retain".  It is not API noise in that branch: it is the
statement `Metric.infDist` and `LinearMap.singularValues_nonneg` both carry, and
it has consumers.  Nothing to do; recorded so the conditional is not re-opened.

*Original disposition:*

**Disposition: Delete or codomain-dependent**

```lean
theorem approximationNumber_nonneg (T : E →L[𝕜] F) (n : ℕ) : 0 ≤ T.approximationNumber n
```

**Proposed target shape**

```lean
-- Delete if approximationNumber : ℝ≥0.
-- If approximationNumber : ℝ, keep:
theorem approximationNumber_nonneg (T) (n) : 0 ≤ T.approximationNumber n
```

- A theorem asserting 0 ≤ x for x : NNReal is pure API noise.

- Retain it only if the codomain is changed to ℝ.

- Search downstream consumers; replace uses with bot_le when NNReal remains.

**Likely adversarial review:** The API-design reviewer is likely to request deletion of a tautological public theorem.

#### P1  ~~lt_approximationNumber_add_pos~~ — RESOLVED 2026-07-27

**Disposition: Renamed to
`exists_rank_le_norm_sub_lt_approximationNumber_add`**, from the existential
conclusion outward as asked (`nnnorm` → `norm` per the codomain decision).
**Reuse audit run:** Mathlib's generic near-minimizer is
`exists_lt_of_ciInf_lt`, which this theorem *uses*; what it adds is the
translation from a `ciInf` over the rank-bounded subtype to a plain `∃ R,
R.rank ≤ n ∧ …`, and every consumer wants the latter.  `Metric.infDist` has no
usable analogue here because the admissible set is a subtype, not a set in the
ambient space.  **Kept public:** it has consumers in another file
(`DavisKahan/OperatorIdeal/ApproximationNumbers/BlockSum.lean`), which is the
item's own criterion, and it is the workhorse behind every inequality in the
file — a fact now stated in its docstring.

*Original disposition:*

**Disposition: Rename / reuse audit**

```lean
theorem lt_approximationNumber_add_pos (T : E →L[𝕜] F) (n : ℕ) {ε : ℝ≥0} (hε : 0 < ε) : ∃ R : E →L[𝕜] F, R.rank ≤ (n : Cardinal) ∧ ‖T - R‖₊ < T.approximationNumber n + ε
```

**Proposed target shape**

```lean
theorem exists_rank_le_nnnorm_sub_lt_approximationNumber_add
    (T : E →L[𝕜] F) (n : ℕ) (hε : 0 < ε) :
    ∃ R, R.rank ≤ n ∧ ‖T - R‖₊ < T.approximationNumber n + ε
```

- Rename from the existential conclusion outward; the current name describes the inequality used in the proof.

- Consider a Metric.infDist or IsGLB lemma if Mathlib already packages near-minimizers of an infimum.

- Keep public only if later approximation-number proofs use it across files.

**Likely adversarial review:** The proof-shaped name is a direct naming-rubric target; reuse may find a generic ciInf near-minimizer theorem.

#### P1  ~~approximationNumber_add_le~~ — RESOLVED 2026-07-27

**Disposition: Renamed to `approximationNumber_add_le_add_norm`**, freeing the
short name for the principal two-index inequality (next item).  This is the
rename the two items ask for as a pair, and Mathlib settles which way round:
`norm_add_le : ‖a + b‖ ≤ ‖a‖ + ‖b‖` carries the short name for subadditivity, so
the subadditive statement gets `approximationNumber_add_le` and the perturbative
one names its extra term.  The suggested symmetric Lipschitz consequence
`|aₙ(T) - aₙ(S)| ≤ ‖T - S‖` was **not** added — no roadmap consumer needs it,
which is the condition the item attaches.  Deriving it from the two-index
inequality at `n = 0` was also declined: `a₀(S) = ‖S‖` makes that route true but
it would invert the dependency order of the file for no gain.

*Original disposition:*

**Disposition: Rename**

```lean
theorem approximationNumber_add_le (T S : E →L[𝕜] F) (n : ℕ) : (T + S).approximationNumber n ≤ T.approximationNumber n + ‖S‖₊
```

**Proposed target shape**

```lean
theorem approximationNumber_add_le_add_nnnorm
    (T S : E →L[𝕜] F) (n : ℕ) :
    (T + S).approximationNumber n ≤ T.approximationNumber n + ‖S‖₊
```

- Rename to expose both terms on the right.

- Add the symmetric Lipschitz consequence \|a_n T - a_n S\| ≤ ‖T-S‖ only if roadmap consumers need it.

- Consider deriving this from the two-index inequality with n=0 if that produces a clean proof and API.

**Likely adversarial review:** The current name is ambiguous with the stronger two-index additive inequality.

#### P1  ~~approximationNumber_add_le_add~~ — RESOLVED 2026-07-27

**Disposition: Renamed to `approximationNumber_add_le`**, exactly as sketched —
it is the principal additive ideal inequality and now carries the canonical
short name, with `norm_add_le` as the naming precedent.  The zero-based index
shift is documented on the theorem itself: `a_{m+n}(T + S) ≤ aₘ(T) + aₙ(S)` is
exact, where one-based `s`-numbers would carry an `m + n - 1`.

*Original disposition:*

**Disposition: Rename family**

```lean
theorem approximationNumber_add_le_add (T S : E →L[𝕜] F) (m n : ℕ) : (T + S).approximationNumber (m + n) ≤ T.approximationNumber m + S.approximationNumber n
```

**Proposed target shape**

```lean
theorem approximationNumber_add_le
    (T S : E →L[𝕜] F) (m n : ℕ) :
    (T + S).approximationNumber (m + n) ≤
      T.approximationNumber m + S.approximationNumber n
```

- This is the principal additive ideal inequality and deserves the shorter canonical name.

- If retaining both additive theorems, give the perturbative corollary the longer name.

- Document the zero-based index shift explicitly.

**Likely adversarial review:** The existing pair of names reverses the likely importance hierarchy and is hard to discover.

#### P0  ~~rank_comp_left_le_of_rank_le~~ — RESOLVED 2026-07-27

**Disposition: Moved out and generalized to `LinearMap`.**  Now
`LinearMap.rank_comp_le_natCast_right` with continuous specializations
`ContinuousLinearMap.rank_comp_le_natCast_right` and
`ContinuousLinearMap.rank_comp_le_left`, in a new dependency-closed module
`ForTauCeti/LinearAlgebra/Dimension/RankComp.lean`, so the operator-ideal file
now carries approximation-number API and no rank plumbing at all — which is the
item's actual objection.

**Privatizing was not available** (the item's first alternative): the theorem has
independent consumers in three `DavisKahan` modules
(`Interop/Spectra/ApproximationNumberMinMax`,
`OperatorIdeal/ApproximationNumbers/Real/Threshold`,
`Experimental/MathAhead/Section4/InfiniteProposition41`) plus the sibling
`ApproximationNumber/FiniteDimensional`.  This is the same situation as
`le_natCast_of_lift_le` above, and it takes the same route.

**Reuse audit run as asked:** Mathlib has `LinearMap.rank_comp_le_left`,
`rank_comp_le_right`, `lift_rank_comp_le_right` and `lift_rank_comp_le`, but no
natural-number-bounded form.  The gap is real and structural rather than
incidental — `rank_comp_le_right` gets rid of the lift by forcing the outer
codomain into the domain's universe, which a `ContinuousLinearMap` between
independent spaces cannot do; bounding by a natural number gets rid of it
instead, because `Cardinal.lift` fixes the image of `ℕ`
(`Cardinal.lift_le_natCast`).  So it closes exactly the "real cross-universe gap
with independent users" the item names as the condition for keeping it.  Stated
at `LinearMap` level it is also no longer "specialized to continuous maps", the
other half of the objection; the continuous forms are one-line specializations
whose point is that `(f ∘L g).rank` needs no unfolding at the call site.  The
argument order now follows Mathlib's `(inner, outer)`, so the four call sites
swapped their two explicit arguments.

*Original disposition:*

**Disposition: Privatize / reuse**

```lean
theorem rank_comp_left_le_of_rank_le {G : Type x} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] (B : F →L[𝕜] G) (R : E →L[𝕜] F) {n : ℕ} (hR : R.rank ≤ (n : Cardinal)) : (B ∘L R).rank ≤ (n : Cardinal)
```

**Proposed target shape**

```lean
-- Prefer existing LinearMap rank lemmas directly.
-- Otherwise keep private:
private theorem rank_comp_le_of_rank_le ...
```

- Search Mathlib for rank_comp_le_left/right and universe-lift variants.

- This is proof plumbing, not approximation-number API.

- Keep private unless it closes a real cross-universe gap with independent users.

**Likely adversarial review:** Reuse review will object to a public rank lemma specialized to continuous maps if the LinearMap theorem already applies.

#### P1  ~~approximationNumber_comp_right_le~~ — RESOLVED 2026-07-27

**Disposition: Renamed to `approximationNumber_comp_le_mul_norm`**
(`aₙ(T ∘L A) ≤ aₙ(T) * ‖A‖`), conclusion-oriented as the item prefers, with the
`nnnorm` in the sketch corrected to `norm`.  `∘L` is kept rather than `.comp`:
it is what the adjacent `ContinuousLinearMap` norm API uses
(`opNorm_comp_le`) and what every consumer in this repository writes.  The
sketched dot-notation form `T.approximationNumber_comp_le A n` **does** work,
since `T` is the first explicit argument, so no separate method wrapper was
added.

*Original disposition:*

**Disposition: Rename / notation**

```lean
theorem approximationNumber_comp_right_le {G : Type x} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] (T : E →L[𝕜] F) (A : G →L[𝕜] E) (n : ℕ) : (T ∘L A).approximationNumber n ≤ T.approximationNumber n * ‖A‖₊
```

**Proposed target shape**

```lean
theorem approximationNumber_comp_le_mul_nnnorm
    (T : E →L[𝕜] F) (A : G →L[𝕜] E) (n : ℕ) :
    (T.comp A).approximationNumber n ≤ T.approximationNumber n * ‖A‖₊
```

- Choose comp notation consistent with ContinuousLinearMap adjacent API.

- A suffix right may be useful, but conclusion-oriented naming is preferable if unambiguous.

- Consider namespace method form T.approximationNumber_comp_le A n.

**Likely adversarial review:** The reviewer will compare naming and composition notation with existing ContinuousLinearMap lemmas.

#### P1  ~~approximationNumber_comp_left_le~~ — RESOLVED 2026-07-27

**Disposition: Renamed to `approximationNumber_comp_le_norm_mul`**
(`aₙ(B ∘L T) ≤ ‖B‖ * aₙ(T)`).  The pair is syntactically parallel as asked, and
the two names differ exactly where the statements differ — which factor keeps
its approximation number — so neither can be used in place of the other by
accident.  Argument order matches `ContinuousLinearMap.comp`: outer map first.

*Original disposition:*

**Disposition: Rename / notation**

```lean
theorem approximationNumber_comp_left_le {G : Type x} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] (B : F →L[𝕜] G) (T : E →L[𝕜] F) (n : ℕ) : (B ∘L T).approximationNumber n ≤ ‖B‖₊ * T.approximationNumber n
```

**Proposed target shape**

```lean
theorem approximationNumber_comp_le_nnnorm_mul
    (B : F →L[𝕜] G) (T : E →L[𝕜] F) (n : ℕ) :
    (B.comp T).approximationNumber n ≤ ‖B‖₊ * T.approximationNumber n
```

- Keep the left/right pair syntactically parallel.

- Use the same argument order as ContinuousLinearMap.comp.

- Test dot-notation discoverability before settling final names.

**Likely adversarial review:** Parallel-form inconsistency will be caught by naming/API review.

#### P2  ~~approximationNumber_comp_comp_le~~ — RESOLVED: kept

**Disposition: Kept, name unchanged.**  Both of the item's proof-quality asks
were already satisfied and were re-verified: it is derived from the two
one-sided inequalities in three lines with no duplicated machinery, and it uses
the canonical `∘L` with `L ∘L T ∘L R` parsed by the standard right
associativity.  It deliberately does **not** follow the conclusion-oriented
renaming of the two one-sided lemmas — spelling this RHS out would give
`…_le_norm_mul_mul_norm`, which is less legible than the shape it describes, and
`comp_comp` already determines the statement uniquely.

*Original disposition:*

**Disposition: Keep / fold proof**

```lean
theorem approximationNumber_comp_comp_le {G : Type x} {H : Type y} [SeminormedAddCommGroup G] [NormedSpace 𝕜 G] [SeminormedAddCommGroup H] [NormedSpace 𝕜 H] (L : F →L[𝕜] G) (T : E →L[𝕜] F) (R : H →L[𝕜] E) (n : ℕ) : (L ∘L T ∘L R).approximationNumber n ≤ ‖L‖₊ * T.approximationNumber n * ‖R‖₊
```

**Proposed target shape**

```lean
theorem approximationNumber_comp_comp_le
    (L : F →L[𝕜] G) (T : E →L[𝕜] F) (R : H →L[𝕜] E) (n : ℕ) :
    (L.comp (T.comp R)).approximationNumber n ≤
      ‖L‖₊ * T.approximationNumber n * ‖R‖₊
```

- This name is likely acceptable.

- Normalize associativity and composition notation to the canonical ContinuousLinearMap API.

- Derive from one-sided inequalities rather than duplicate proof machinery.

**Likely adversarial review:** Low naming risk; proof-quality review may request deriving it from the two one-sided lemmas.

#### P2  ~~approximationNumber_smul~~ — RESOLVED 2026-07-27

**Disposition: `@[simp]` added; name and statement unchanged** (`‖c‖`, not
`‖c‖₊`, per the codomain decision).  Both of the item's conditions were checked
rather than assumed: the zero scalar is handled inside the proof with no
hypothesis on `c`, and the left-hand side `(c • T).approximationNumber n` is a
sound simp target because it strictly decomposes.

*Original disposition:*

**Disposition: Keep / add simp**

```lean
theorem approximationNumber_smul (c : 𝕜) (T : E →L[𝕜] F) (n : ℕ) : (c • T).approximationNumber n = ‖c‖₊ * T.approximationNumber n
```

**Proposed target shape**

```lean
@[simp] theorem approximationNumber_smul
    (c : 𝕜) (T : E →L[𝕜] F) (n : ℕ) :
    (c • T).approximationNumber n = ‖c‖₊ * T.approximationNumber n
```

- The name and statement are characteristic and should probably be simp.

- Confirm zero scalar is handled without nonzero assumptions.

- If codomain becomes ℝ, use ‖c‖ rather than ‖c‖₊.

**Likely adversarial review:** Low risk after the codomain decision.

### 5.2 Adjoint.lean

| **Current file** | ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Adjoint.lean |
| --- | --- |
| **Proposed disposition** | Keep one public adjoint-invariance theorem; private rank transport stays implementation detail. |
| **Readiness** | High after Basic is settled. |
| **Primary review risks** | Potential duplication with generic rank-adjoint API; missing simp annotation; RCLike/CompleteSpace assumptions. |
| **Likely PR slice** | PR A2. |

#### P1  approximationNumber_adjoint

**Disposition: Keep / annotate**

```lean
theorem approximationNumber_adjoint (T : E →L[𝕜] F) (n : ℕ) : T.adjoint.approximationNumber n = T.approximationNumber n
```

**Proposed target shape**

```lean
@[simp] theorem approximationNumber_adjoint
    (T : E →L[𝕜] F) (n : ℕ) :
    T.adjoint.approximationNumber n = T.approximationNumber n
```

- Add @[simp] if it orients toward eliminating adjoints and does not loop.

- Keep the inequality helper private.

- Check whether CompleteSpace is required on both spaces only because adjoint is defined there; retain natural assumptions.

**Likely adversarial review:** This is a clean characteristic theorem; the main review question is whether the private rank proof duplicates Mathlib.

### 5.3 FiniteDimensional.lean

| **Current file** | ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/FiniteDimensional.lean |
| --- | --- |
| **Proposed disposition** | Keep the Eckart-Young mathematics; redesign the public singular-value expression. |
| **Readiness** | Medium-high. |
| **Primary review risks** | Plural singularValues naming, raw NNReal constructor in conclusions, possible duplicate truncation API. |
| **Likely PR slice** | PR A2 after adjoint. |

#### P0  ~~singularValues_le_norm_sub_of_rank_le~~ — RESOLVED 2026-07-27

**Disposition: restated over a new `ContinuousLinearMap`-level accessor.**  All
three §5.3 P0s shared one root cause — every public statement said
`T.toLinearMap.singularValues n`, leaking the `ContinuousLinearMap → LinearMap`
coercion into the statement and into every downstream proof — so they are fixed
together by the new module
`ForTauCeti/Analysis/InnerProductSpace/SingularValues.lean`:
`ContinuousLinearMap.singularValues T := T.toLinearMap.singularValues`, with the
`@[simp]` bridge `toLinearMap_singularValues` (oriented so `simp` *removes* the
coercion) and one-line delegations for the facts the operator layer uses.  The
four statements `singularValues_le_norm_sub_of_rank_le`,
`singularValues_le_approximationNumber`, `approximationNumber_le_singularValues`
and the headline `approximationNumber_eq_singularValues` are now stated over it;
the proofs convert back with a single `rw [← toLinearMap_singularValues]` where
they need Mathlib's `LinearMap`-level lemmas, so nothing is duplicated.

**Deviation from the review sketch, deliberate:** the sketch asks for a
*singular* `singularValue` "unless the existing Mathlib function is irrevocably
plural".  It is — Mathlib's object is the whole `Finsupp` sequence `ℕ →₀ ℝ`, and
`T.singularValues n` is application to it — so the accessor stays plural.  A
singular accessor would have to be a second definition wrapping the first, i.e.
exactly the duplication the module exists to remove.

**Stale half of the sketch:** the `⟨value, proof⟩ : NNReal` constructor noise it
flags in `singularValues_le_approximationNumber` no longer exists; the codomain
decision (§5.1 decision 2) made the whole API real-valued, so that statement had
already lost its constructor.

*Original disposition:*

**Disposition: API bridge**

```lean
theorem singularValues_le_norm_sub_of_rank_le (T R : E →L[𝕜] F) (n : ℕ) (hR : R.rank ≤ (n : Cardinal)) : T.toLinearMap.singularValues n ≤ ‖T - R‖
```

**Proposed target shape**

```lean
theorem singularValue_le_norm_sub_of_rank_le
    (T R : E →L[𝕜] F) (hR : R.rank ≤ n) :
    T.singularValue n ≤ ‖T - R‖
```

- Prefer a singular-value accessor on ContinuousLinearMap rather than T.toLinearMap.singularValues in public statements.

- Use singularValue singular unless the existing Mathlib function is irrevocably plural.

- Move the index next to T according to adjacent API conventions.

**Likely adversarial review:** The current signature leaks conversion to LinearMap and a plural function name into every consumer.

#### P0  ~~singularValues_le_approximationNumber~~ — RESOLVED 2026-07-27 (see above)

*Original disposition:*

**Disposition: Redesign codomain bridge**

```lean
theorem singularValues_le_approximationNumber (T : E →L[𝕜] F) (n : ℕ) : (⟨T.toLinearMap.singularValues n, T.toLinearMap.singularValues_nonneg n⟩ : NNReal) ≤ T.approximationNumber n
```

**Proposed target shape**

```lean
theorem singularValue_le_approximationNumber
    (T : E →L[𝕜] F) (n : ℕ) :
    T.singularValueNNReal n ≤ T.approximationNumber n
```

- Introduce exactly one canonical nonnegative singular-value wrapper if NNReal is retained.

- Do not repeat ⟨value, proof⟩ in public signatures.

- If approximationNumber becomes real-valued, state the theorem directly over ℝ.

**Likely adversarial review:** Constructor noise and mixed codomains are likely API-design findings.

#### P1  approximationNumber_le_singularValues

**Disposition: Possibly privatize**

```lean
theorem approximationNumber_le_singularValues (T : E →L[𝕜] F) (n : ℕ) : T.approximationNumber n ≤ (⟨T.toLinearMap.singularValues n, T.toLinearMap.singularValues_nonneg n⟩ : NNReal)
```

**Proposed target shape**

```lean
theorem approximationNumber_le_singularValue
    (T : E →L[𝕜] F) (n : ℕ) :
    T.approximationNumber n ≤ T.singularValueNNReal n
```

- Keep syntactically parallel with the reverse inequality.

- If only equality is meant to be public, make both inequalities private.

- Avoid exporting proof decomposition unless consumers use each direction.

**Likely adversarial review:** The API reviewer may ask why both inequalities are public if equality is the real product.

#### P0  ~~approximationNumber_eq_singularValues~~ — RESOLVED 2026-07-27 (statement now `T.approximationNumber n = T.singularValues n`, no coercion; see above)

*Original disposition:*

**Disposition: Headline API**

```lean
theorem approximationNumber_eq_singularValues (T : E →L[𝕜] F) (n : ℕ) : T.approximationNumber n = (⟨T.toLinearMap.singularValues n, T.toLinearMap.singularValues_nonneg n⟩ : NNReal)
```

**Proposed target shape**

```lean
@[simp] theorem approximationNumber_eq_singularValue
    (T : E →L[𝕜] F) (n : ℕ) :
    T.approximationNumber n = T.singularValueNNReal n
```

- Rename singular and remove raw constructor.

- State finite-dimensional assumptions visibly at section level and in the docstring.

- Consider whether the theorem should be the canonical definition bridge used to simplify approximation numbers in finite dimensions.

**Likely adversarial review:** This is the headline theorem and should be much cleaner than the current right-hand side.

### 5.4 MinMax.lean

| **Current file** | ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/MinMax.lean |
| --- | --- |
| **Proposed disposition** | Keep the lower-bound principle, but state it at the natural dimension level and add the actual min-max endpoint later. |
| **Readiness** | Medium. |
| **Primary review risks** | Proof-oriented name; equality finrank=n+1 stronger than needed; family corollary may be API clutter. |
| **Likely PR slice** | PR A3. |

#### P0  ~~lowerBound_le_approximationNumber_of_finrank~~ — RESOLVED 2026-07-27

**Disposition: generalized, and split into a primary result plus two derived
forms.**  The primary statement is now
`ContinuousLinearMap.le_approximationNumber_of_lt_rank`, over
`(n : Cardinal) < Module.rank 𝕜 V` with the **homogeneous** hypothesis
`c * ‖x‖ ≤ ‖T x‖`.  Both changes are real generalizations, not renames:

* stating the size hypothesis on `Module.rank` rather than `finrank`
  **removes the `[FiniteDimensional 𝕜 V]` instance entirely** — an
  infinite-dimensional test subspace satisfies `n < Module.rank 𝕜 V` for every
  `n`, and the proof never needed more than "`V` is too big to be killed by a
  rank `≤ n` map".  The exact dimension `finrank 𝕜 V = n + 1` the review
  flagged was doing no work at all;
* the homogeneous bound says something at `x = 0` and scales, where a
  unit-vector premise does neither.

`le_approximationNumber_of_finrank_lt` recovers the classical finite-dimensional
unit-vector form (the conversion needs **no** sign hypothesis on `c`: at `x = 0`
the bound reads `c * 0 ≤ 0`, and elsewhere it is a rescaling), and
`le_approximationNumber_of_linearIndependent` the family form.  All three are
named from the conclusion outward; `lowerBound` is gone, since it never named an
object in the statement.  No aliases retained; 8 call sites repointed.

**Not in scope, and deliberately not faked:** the review's fourth ask, "the
ultimate API should expose a supremum/max-min formula, with this as a lemma".
Only *this* half of the min--max characterization is unconditional in infinite
dimensions, which is precisely what roadmap milestone B.4 says the two-sided
package must be honest about; inventing a `⨆`-form here would paper over that.

*Original disposition:*

**Disposition: Generalize signature**

```lean
theorem lowerBound_le_approximationNumber_of_finrank (T : E₁ →L[𝕜] F₁) (n : ℕ) (V : Submodule 𝕜 E₁) [FiniteDimensional 𝕜 V] (hVdim : finrank 𝕜 V = n + 1) (c : NNReal) (hV : ∀ x : V, ‖x‖ = 1 → c ≤ ‖T (x : E₁)‖₊) : c ≤ T.approximationNumber n
```

**Proposed target shape**

```lean
theorem le_approximationNumber_of_finrank_lt
    (hVdim : n < finrank 𝕜 V)
    (hV : ∀ x : V, ‖x‖ = 1 → c ≤ ‖T x‖₊) :
    c ≤ T.approximationNumber n
```

- Generalize finrank V = n+1 to n < finrank V unless the proof or intended theorem needs exact dimension.

- Rename from the conclusion outward; lowerBound is not an object in the statement.

- Consider replacing c : NNReal plus unit norm with a bound c * ‖x‖ ≤ ‖T x‖ that handles x=0 and scales naturally.

- The ultimate API should expose a supremum/max-min formula, with this as a lemma.

**Likely adversarial review:** Generality review will likely flag exact dimension equality and proof-oriented naming.

#### P1  ~~lowerBound_le_approximationNumber_of_linearIndependent~~ — RESOLVED 2026-07-27

**Disposition: kept public, renamed `le_approximationNumber_of_linearIndependent`.**
The open question was "decide whether this family wrapper has independent
consumers; otherwise keep private".  **It has 8, across 6 `DavisKahan` modules** —
it is how every downstream consumer actually applies the bound, because a
spanning family is what the perturbation arguments produce.  So it is not a
forgetful convenience wrapper, and that evidence is now recorded on the theorem
itself rather than left as an open question.  The homogeneous-inequality
suggestion is satisfied one level down, at the primary
`le_approximationNumber_of_lt_rank`; this wrapper keeps the unit-vector premise
its callers supply.

*Original disposition:*

**Disposition: Corollary or private**

```lean
theorem lowerBound_le_approximationNumber_of_linearIndependent (T : E₁ →L[𝕜] F₁) (n : ℕ) (v : Fin (n + 1) → E₁) (hv : LinearIndependent 𝕜 v) (c : NNReal) (hV : ∀ x ∈ Submodule.span 𝕜 (Set.range v), ‖x‖ = 1 → c ≤ ‖T x‖₊) : c ≤ T.approximationNumber n
```

**Proposed target shape**

```lean
theorem le_approximationNumber_of_linearIndependent
    (hv : LinearIndependent 𝕜 v)
    (hV : ∀ x ∈ span 𝕜 (range v), c * ‖x‖ ≤ ‖T x‖) :
    c ≤ T.approximationNumber n
```

- Decide whether this family wrapper has independent consumers; otherwise keep private.

- Prefer a homogeneous inequality rather than a unit-vector premise.

- Derive it in one line from the submodule theorem.

**Likely adversarial review:** An API reviewer may classify this as a forgetful convenience wrapper with no need in the roadmap.

## 6. ~~Courant-Fischer and finite spectral API~~ — RESOLVED, removed from backlog

All §6 items were executed on the canonical ForTauCeti copy (2026-07-24, edward;
see the name map in `dev/tauceti/formathlib-to-fortauceti-migration.md`):
`specSubspace` became `OrthonormalBasis.spanIndices` over a general finite index
type and `Set` selection, with the full basic API (membership iff, Finset/Set
dimension, orthogonal complement) in the new
`ForTauCeti/Analysis/InnerProductSpace/BasisSpan.lean`; the eigenvalue results
moved into the `LinearMap.IsSymmetric` namespace with `_apply_` naming and the
misquantified `forall_unit_vector_…` renamed to
`exists_submodule_forall_unit_eigenvalue_le_re_inner`; the missing
characteristic endpoint is now proved
(`LinearMap.IsSymmetric.eigenvalues_eq_iSup_iInf_re_inner`, the sup-inf
Courant–Fischer equality); Weyl is exposed for self-adjoint continuous linear
maps as `TauCeti.abs_eigenvalue_sub_eigenvalue_le_norm` with `‖T − S‖` on the
right-hand side and no `toContinuousLinearMap` in the signature;
`eigenvalues_le_eigenvalues_of_re_inner_le` became
`LinearMap.IsSymmetric.eigenvalue_mono`.

Still open, deliberately (recorded here so the roadmap can decide):

- **`hn : finrank 𝕜 E = n` threading** is retained — Mathlib's
  `IsSymmetric.eigenvalues`/`eigenvectorBasis` API itself takes `hn`, so hiding
  it would require wrapping the upstream API, which §3 forbids.
- **Loewner-order form of `eigenvalue_mono`** (premise `T ≤ S` instead of the
  quadratic-form inequality) waits until the target library's operator order
  for `E →L[𝕜] E` is the settled premise language.

## 7. ~~Operator modulus and absolute value convergence~~ — RESOLVED, removed from backlog

Executed 2026-07-24 (edward). There were in fact **three** importable copies,
not two: `TauCeti.operatorAbs` (square), the staged ForTauCeti
`rectangularOperatorModulus` (dead — zero importers), and a still-live
redefinition of `rectangularOperatorModulus` inside
`DavisKahan/OperatorIdeal/ApproximationNumbers/OperatorModulus.lean`.

All three are replaced by one canonical rectangular definition,
`ContinuousLinearMap.modulus` in
`ForTauCeti/Analysis/InnerProductSpace/OperatorModulus.lean`, with dot notation
and the full API (`modulus_nonneg`, `modulus_isSelfAdjoint`, `adjoint_modulus`,
`modulus_mul_self`, `eq_modulus_of_nonneg_of_mul_self_eq`, `norm_modulus_apply`
and `norm_modulus` as `simp`, `norm_modulus_comp`, `norm_comp_modulus`,
`modulus_commute_modulus`, plus the endomorphism specializations
`modulus_eq_sqrt_star_mul_self` / `modulus_mul_self_eq_star_mul_self`).

Beyond deduplication the following backlog concerns were answered:

- the square-only composition laws `norm_operatorAbs_mul` / `norm_mul_operatorAbs`
  are **generalized to rectangular operators** and reproved — the left law is
  now a one-line consequence of the pointwise isometry rather than a
  C⋆-identity computation, and the right law is that law conjugated by the
  isometric adjoint.  The backlog's open question ("check whether the right
  side should be `D * T` or `D * T.adjoint`") is settled: it is `T.adjoint`,
  and the docstring explains why (the two sides act on different spaces);
- uniqueness and the commutation lemma are likewise stated rectangularly (the
  latter for operators with a common *source* and unrelated targets);
- `rectangularGram_nonneg` became `adjoint_comp_self_nonneg`, documented as the
  `0 ≤ ·` form of Mathlib's `isPositive_adjoint_comp_self`.

`operatorAbs` survives only as a reducible alias in a documented transitional
shim (`OperatorAbsoluteValue.lean`, not upstream-bound) so the ~80 Davis--Kahan
references keep compiling; delete per declaration as consumers migrate.

Still open, deliberately: whether the canonical name should be `modulus`,
`abs`, or `operatorAbs` is a naming call for the roadmap — Mathlib has no
operator absolute value today, so there is no precedent to match; `modulus`
was chosen because `abs` collides with lattice/`|·|` expectations.

## 8. Inner-product-space utilities

### 8.1 ~~CenteredScatter.lean~~ — RESOLVED, removed from backlog

Executed 2026-07-27 (jon). All three P0 items settled; the file builds clean with no
deprecation warnings and every declaration stays axiom-clean.

**P0 `appendFin` — DELETED.** It was exactly `Fin.snoc`, so the "classic reuse-rubric
target" the backlog predicted was real. The two `@[simp]` lemmas `appendFin_castSucc` /
`appendFin_last` went with it, replaced by upstream `Fin.snoc_castSucc` / `Fin.snoc_last`.
FINDING for the one consumer: `Fin.lastCases` and `Fin.snoc` are **not** definitionally
equal — `snoc` transports along `cast` — so `DkpsQuench2026/Spectral/GramSpectrum.lean`,
which had bridged the two by `rfl`, now needs a two-line `funext`/`Fin.lastCases`
comparison. Its statement still uses `Fin.lastCases` because that spelling propagates into
`DkpsQuench2026/Spectral/Regularity.lean`, outside this lane.

**P0 `centeredScatter` — moved to `E →L[𝕜] E`.** Its summands `rankOne 𝕜 a a` are already
continuous, so the old `E →ₗ[𝕜] E` codomain discarded continuity for nothing. Verified
before committing: `ContinuousLinearMap.IsPositive` and the Löwner order (`le_def`) both
exist at CLM level and — contrary to the obvious worry — need **no** `CompleteSpace`
hypothesis, so the move costs no generality. Not done: the `Finset`/`Fintype`
generalization. The add-one identity is intrinsically about extending `Fin n` to
`Fin (n+1)`, so a `Finset` restatement would be `insert`-indexed and is a genuine redesign
of the headline theorem plus its 60-line scalar-algebra proof, not a signature edit.

**P0 `finiteMean` — reuse audit says KEEP, and it is not a duplicate.** Checked against the
compiler, not by inspection:

- `Finset.expect` (Mathlib's canonical finite average, `𝔼 i ∈ s, f i`) requires
  `Module ℚ≥0 M`. That instance does **not** synthesize for a general `𝕜`-inner-product
  space — confirmed by elaborating `Finset.expect Finset.univ z` against
  `[RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]`, which fails on
  `Module ℚ≥0 E`.
- `Finset.centroid` *does* typecheck in this setting, so it is a live candidate — but
  `Finset.affineCombination` is defined against `Classical.arbitrary`, so the centroid of
  the empty family is nonconstructive junk. `finiteMean` returns `0` there and
  `finiteMean_append` is deliberately stated to hold *at* `n = 0`, so a swap would have to
  re-open that boundary case. (This sharper reading of `centroid`, and the fact that
  `Module ℚ≥0 E` fails because `NormedSpace ℝ E` is reachable only through the
  non-instance `InnerProductSpace.rclikeToReal` / `NormedSpace.restrictScalars`, are
  edward's — independently probed while scoping §8.2 and posted to the LANES cross-lane
  findings section. Both lanes reached the same conclusion separately.)

Either would force non-`𝕜` scalars into a computation that is otherwise pure `𝕜`-module
algebra (`inner_smul_left`, `match_scalars`, `field_simp`). The audit result is recorded in
the module docstring so the next reviewer does not repeat it. The `Fin n` → `Finset`
generalization the backlog also asked for is deferred with the headline theorem, above.

Also fixed in passing: the module docstring's "Main results" list still pointed at
`ForMathlib.*` names for declarations that now live in `TauCeti.*` — stale links that would
not have resolved in generated docs.

### 8.2 ~~NearIsometry.lean~~ — P0 RESOLVED 2026-07-27

| **Current file** | ForTauCeti/Analysis/InnerProductSpace/NearIsometry.lean (rewritten), ForTauCeti/Analysis/InnerProductSpace/PolarIsometry.lean (new), ForTauCeti/Analysis/SpecialFunctions/Sqrt.lean (new) |
| --- | --- |
| **Disposition** | **Done.**  Canonical object defined over `ℂ`; real finite-dimensional statement now returns the polar factorization; constant sharpened; scalar lemmas moved out. |

**What the review asked for, and what was done.**

- *"First prove the natural general object: an isometric embedding/partial
  isometry from polar decomposition."*  `ContinuousLinearMap.polarIsometry M =
  M ∘L Ring.inverse M.modulus` is now a **definition**, over arbitrary complex
  Hilbert spaces `E →L[ℂ] F` — no finite-dimensionality, no equal-dimension
  assumption, and rectangular.  It is total in `M` (junk-valued off the
  bounded-below locus, in the style of `Ring.inverse`), so it rewrites and
  composes; the isometry hypothesis `IsUnit M.modulus` is carried explicitly by
  each theorem.  Supporting API: `polarIsometry_comp_modulus` (the polar
  identity `W ∘L |M| = M`), `norm_polarIsometry_apply`, `isometry_polarIsometry`,
  `isUnit_modulus_iff`.

- *"Derive a `LinearIsometryEquiv` only with finite-dimensional equal-rank or
  explicit surjectivity."*  Done: `polarLinearIsometry` is the bundled
  `E →ₗᵢ[ℂ] F`; `polarLinearIsometryEquiv` takes surjectivity as an explicit
  hypothesis, with `surjective_polarIsometry_of_surjective` supplying it from
  surjectivity of `M`.  The hidden `injective_iff_surjective` step of the old
  proof is gone from the general statement (it survives only inside the real
  finite-dimensional proof, where it is genuinely available).

- *"Generalize from `ℝ` to `RCLike` if the proof is not genuinely ordered-real
  specific."*  **Finding: it is not `RCLike`-generalizable as one theorem, and
  the reason is an upstream instance gap, not the proof.**  The canonical object
  needs the operator square root `|M| = (M⋆ M)^(1/2)`, which Mathlib supplies
  only through the continuous functional calculus, and the C⋆-algebra instance
  on `E →L[𝕜] E` is registered **only for `𝕜 = ℂ`**
  (`Mathlib/Analysis/CStarAlgebra/ContinuousLinearMap.lean`).  So the general
  development is complex, and the real case keeps its own eigenbasis proof —
  which is now justified rather than accidental, and is documented as such in
  both module docstrings.  The real file's `TODO(RCLike)` is retained for the
  *statement* generality (the eigenbasis machinery does work over `RCLike`).

- *"Avoid two public theorems with the same basename in `LinearMap` and
  `ContinuousLinearMap`."*  The two levels now take genuinely different
  hypotheses (pointwise quadratic form vs. operator norm `‖M⋆M - 1‖ ≤ δ`), and
  the `ContinuousLinearMap` one is a three-line corollary through a `private`
  Cauchy--Schwarz bridge rather than a parallel development.

- *"P1 `abs_one_sub_inv_sqrt_le`: place this scalar lemma in `Real.Sqrt` or a
  dedicated elementary analysis file, not inside near-isometry operator
  theory."*  Moved to the new `ForTauCeti/Analysis/SpecialFunctions/Sqrt.lean`,
  together with the new sharp lemma `abs_sqrt_sub_one_le_abs_sub_one`
  (`|√μ - 1| ≤ |μ - 1|`, `0 ≤ μ`).  **Deviation from the review sketch,
  deliberate:** the sketch proposed adding an explicit `0 ≤ δ` hypothesis.  Not
  done — `0 ≤ δ` is forced by `hμ : |μ - 1| ≤ δ`, and a redundant hypothesis is
  worse Mathlib style than a derivable one.  The derivation is now stated in the
  docstring, which is what the review was actually after ("hides how positivity
  is obtained").

**Mathematical improvement beyond the requested polish.**

Returning the factorization instead of only the estimate makes the constant
sharp.  Because `W` is an isometry and `M x = W (S x)`,
`‖M x - W x‖ = ‖S x - x‖` exactly, so the operator bound *is* the scalar bound
on the eigenvalues of the Gram operator.  Consequences:

- the constant improves from `2 * δ` to **`δ`**, in both the complex and the
  real development;
- the hypothesis weakens from `δ ≤ 1 / 2` to **`δ < 1`** (needed only to make
  `M` bounded below);
- the old proof's lossy steps — `‖M z‖ ≤ √(1 + δ) ‖z‖` and `√(1 + δ) ≤ 2` — are
  deleted outright, and so is the inverse-square-root scalar lemma from the
  proof path (`|√μ - 1| ≤ |μ - 1|` replaces it and needs no smallness
  hypothesis).

The real statement `exists_linearIsometryEquiv_comp_polarFactor` additionally
pins the factor down: `S` is symmetric with `S ∘ S = Mᵀ ∘ M`, i.e. it *is* the
modulus of `M`, so the canonical object is recoverable from the existential.

**Compatibility.**  The two historical statements
`TauCeti.{LinearMap,ContinuousLinearMap}.exists_linearIsometryEquiv_norm_sub_le`
(constant `2 * δ`, hypothesis `δ ≤ 1 / 2`) are **kept verbatim** as one-line
corollaries, because they are the form quoted by `Acharyya2025.PolarFactor` (a
paper-fidelity wrapper, which must keep the printed constant) and by the
challenge comparator, whose export check compares full types.  Fixed along the
way: `comparator/pending-near-isometry.json` still named the pre-dedup
`ForMathlib.*` declarations and could never have passed; repointed to
`TauCeti.*` and verified with `scripts/check_comparator_signatures.py`.
**The same staleness affects ~20 other comparator configs (36 names) — repo-wide
follow-up, not fixed here.**


### 8.3 ~~OrthogonalSeries.lean~~ — RESOLVED, removed from backlog

Executed 2026-07-27 (jon). The backlog asked for an "exact duplicate audit" of the whole
file. It found one.

**Mathlib's `OrthogonalFamily` API contains statement-for-statement counterparts of three of
the five declarations** (`Analysis/InnerProductSpace/Subspace.lean`):

| this file | upstream |
| --- | --- |
| `norm_sq_finset_sum_of_pairwise_inner_eq_zero` | `OrthogonalFamily.norm_sum` |
| `norm_sq_sdiff_sum_of_pairwise_inner_eq_zero` | `OrthogonalFamily.norm_sq_sdiff_sum` |
| `summable_iff_norm_sq_summable_of_pairwise_inner_eq_zero` | `OrthogonalFamily.summable_iff_norm_sq_summable` |

The only difference is the indexing: upstream takes a family of *subspaces* `G i` with
isometries `V i : G i →ₗᵢ E`; this file takes *vectors* with pairwise `⟪f i, f j⟫ = 0`.

**FINDING — the missing piece is a constructor, not the theorems.** Mathlib's only bridge
into `OrthogonalFamily` from vectors is `Orthonormal.orthogonalFamily`, which requires
*unit* vectors; there is nothing for a merely pairwise-orthogonal family. So the file's real
contribution is that constructor, now stated as
`orthogonalFamily_of_pairwise_inner_eq_zero`: the lines `𝕜 ∙ f i` with `subtypeₗᵢ`, proved
in one line from `Submodule.isOrtho_span`. Because `V i (l i)` is `f i` definitionally, every
downstream statement is a specialization needing no rewriting.

Result: the hand-rolled Pythagoras induction, the symmetric-difference identity and the
ε–N Cauchy-criterion argument — roughly 90 lines of proof duplicating upstream — are gone.
`norm_sq_sdiff_sum_of_pairwise_inner_eq_zero` became unused once the Cauchy argument was
replaced by the upstream equivalence and was **deleted outright**; the backlog had only
proposed privatizing it.

Kept, because they have no `OrthogonalFamily` counterpart upstream and carry the file's
remaining content: `summable_of_pairwise_inner_eq_zero_of_partial_sum_norm_le` (a uniform
bound on all finite partial sums gives summability, with no separate closedness theorem) and
`HasSum.norm_sq_eq_tsum_of_pairwise_inner_eq_zero` (Parseval).

Naming: only `norm_sq_finset_sum_…` → `norm_sum_sq_…` was renamed (`finset` was redundant —
the argument is visibly a `Finset`). The other names deliberately kept their
`_of_pairwise_inner_eq_zero` suffix to mirror upstream `OrthogonalFamily.*` spelling; there
is no bundled Mathlib predicate for pairwise-orthogonal *vectors* to shorten them with, so
the backlog's proposed `..._of_pairwise_orthogonal` would name a predicate that does not
exist. The sole consumer,
`DavisKahan/Alternative/OperatorIdeal/HilbertSchmidt/ColumnExpansion.lean`, uses only
unrenamed declarations and needed no edit.

Not done: the `TauCeti.OrthogonalSeries` namespace is itself non-Mathlib-idiomatic (upstream
would put these at root or under `OrthogonalFamily`), but changing it is consumer churn
without API benefit and is left for the namespace pass.

## 9. ~~C*-algebra and matrix helpers~~ — RESOLVED, removed from backlog

### 9.1 ~~SelfAdjointGapInverse.lean~~ — RESOLVED, removed from backlog

Executed 2026-07-27 (jon). Both P0 items are settled; the file now carries three
declarations, all axiom-clean.

**Reuse audit result (P0 `norm_le_of_spectrum_subset_Icc`): no direct Mathlib
replacement exists, but the honest statement is an iff.** Mathlib's isometric CFC
layer supplies `norm_cfc_le_iff`, and specializing it to the identity through
`cfc_id` gives both directions at once, so the one-directional form was strictly
weaker than what the same proof yields. Kept and strengthened as
`TauCeti.IsSelfAdjoint.norm_le_iff_spectrum_subset_Icc :
‖a‖ ≤ r ↔ spectrum ℝ a ⊆ Set.Icc (-r) r` (three-line proof). The four call sites
now use `.mpr`; the one-directional lemma was **not** retained, per "do not carry
both APIs".

**Redesign result (P0 `exists_two_sided_inverse_of_spectrum_gap`): the existential
is gone, split into two declarations.**

- `TauCeti.isUnit_of_forall_le_abs (hr : 0 < r)
  (hσ : ∀ x ∈ spectrum ℝ a, r ≤ |x|) : IsUnit a`
- `TauCeti.IsSelfAdjoint.norm_ringInverse_le (ha : IsSelfAdjoint a) (hr : 0 < r)
  (hσ : ∀ x ∈ spectrum ℝ a, r ≤ |x|) : ‖Ring.inverse a‖ ≤ r⁻¹`

Two findings beyond the planned redesign:

- **Invertibility needs neither self-adjointness nor a C\*-algebra.** It is
  `spectrum.isUnit_of_zero_notMem` plus "a gap around `0` excludes `0`", so
  `isUnit_of_forall_le_abs` is stated for `[Ring A] [Algebra ℝ A]` and sits
  outside the `IsSelfAdjoint` namespace. Carrying `IsSelfAdjoint` there would have
  been an unused hypothesis — exactly what §3 tells reviewers to attack.
- **The old proof reimplemented Mathlib.** Its ~30 lines built the inverse by hand
  from two `cfc_mul`/`cfc_congr` round trips; that is precisely `cfcUnits` /
  `cfc_inv`, and `cfc_ringInverse_id` states the needed identity outright. The new
  proof is four lines and, unlike the old one, returns the *canonical*
  `Ring.inverse` rather than an anonymous witness.

The hypothesis was left as `∀ x ∈ spectrum ℝ a, r ≤ |x|` rather than the
`spectrum ℝ a ∩ Set.Ioo (-r) r = ∅` or `Metric.infDist` alternatives the backlog
floated: all four call sites discharge it pointwise (`rcases` on a two-sided
spectral hypothesis, then `neg_le_abs`/`le_abs_self`), so the ∀-form is what
consumers actually produce, and it is the form `norm_cfc_le` consumes.

Consumers repointed (8 call sites, 4 files): `DavisKahan/Sylvester/GenuineSpectrum.lean`,
`DavisKahan/TanTheta/GenuineSpectrum.lean`,
`DavisKahan/TanTheta/UnboundedGenuineSpectrum.lean`,
`DavisKahan/Experimental/InfiniteDimensional/Riccati/BoundedExistence.lean`. Three
of the eight destructured a `_hJ2` they never used — direct evidence that the
bundled conjunction was over-packaged.

### 9.2 ~~Matrix/Spectrum.lean~~ — RESOLVED, removed from backlog

Executed 2026-07-27 (jon). Renamed as proposed, and the backlog's own question —
"check whether the natural conclusion is support/cardinality, with this pointwise
theorem as a corollary" — resolved in the affirmative: it is, and both supporting
facts were buried inside the single proof.

Reuse audit: Mathlib indexes Hermitian eigenvalues twice (`eigenvalues₀`, sorted
and `Fin (Fintype.card n)`-indexed; `eigenvalues`, reusing the matrix index `n`,
*defined* from the first along an index equivalence), but states the basic theory
only for the second. Upstream `eigenvalues₀` carries just `eigenvalues₀_antitone`
and the charpoly identities — neither `rank_eq_card_non_zero_eigs` nor
`PosSemidef.eigenvalues_nonneg` has a sorted counterpart. So this was a
basic-theory build-out, not a rename.

The file now carries three declarations, all axiom-clean:

- `Matrix.IsHermitian.rank_eq_card_non_zero_eigenvalues₀` — the rank counts the
  nonzero *sorted* eigenvalues, in the exact shape of Mathlib's unsorted
  `rank_eq_card_non_zero_eigs`. **Positive semidefiniteness is not needed**; the
  old proof carried it only because the statement it served did.
- `Matrix.PosSemidef.eigenvalues₀_nonneg` — sorted counterpart of
  `PosSemidef.eigenvalues_nonneg`.
- `Matrix.PosSemidef.eigenvalues₀_eq_zero_of_rank_le` — the renamed headline, now
  a short counting corollary, with `i` implicit as the backlog asked.

FINDING: positive semidefiniteness is **essential** to the headline and not merely
convenient — a rank-one Hermitian matrix whose nonzero eigenvalue is negative sorts
that eigenvalue *last*, so its tail is not zero. It is inessential to the rank
count. Separating the two is the substance of this pass, and the reason the
counting lemma is the more reusable export.

The index equivalence relating the two indexings is kept **private**: it is an
implementation detail of Mathlib's `eigenvalues`, and all three public statements
avoid it.

## 10. ~~Measure-theory helpers~~ — RESOLVED, removed from backlog

Executed 2026-07-27 (jon). **The reuse audit cleared the section: nothing was deleted.**
That is the opposite of what this section's framing anticipated ("Generalize and relocate
only after exact Mathlib reuse audit", and for `one_sub_measure_compl_le` specifically,
"may not merit a new public declaration"). Each candidate was checked by putting the goal
to `exact?` against Mathlib, not by reading names.

**`one_sub_measure_compl_le` — KEEP.** `exact?` cannot close
`1 - μ sᶜ ≤ μ s` for `[IsProbabilityMeasure μ]`. Upstream `prob_compl_eq_one_sub₀` needs
`NullMeasurableSet s` and `prob_compl_le_one_sub_of_le_prob` needs `MeasurableSet s`; the
measurability-free form genuinely does not exist, and it is the form high-probability events
are consumed in, where the event sets are often not easily measurable.

**`measurableSet_exists_mem_le` — KEEP, and the P0 request is now satisfied.** The backlog
asked for the missing canonical measurable-infimum object, with the set form derived. Added:

- `TauCeti.exists_mem_le_iff_iInf_le` — on a nonempty compact `S` the two agree, because the
  infimum is attained. Stated with `omit [MeasurableSpace Ω]`: it is pure order/topology, and
  the linter caught that the instance was along for the ride.
- `TauCeti.measurable_iInf_of_isCompact` — `Measurable fun ω => ⨅ y : S, F y ω`.

FINDING on the direction of the derivation: the backlog proposed deriving the set form *from*
the infimum lemma. It is done the other way round, because the existential form is what the
uncountable-index argument actually proves and what consumers use, while the infimum
statement follows from it in four lines through `measurable_of_Iic`. Deriving in the proposed
direction would have meant rewriting the separability/sequential-compactness proof for no
gain. Recorded here so the choice is not re-litigated.

Why the infimum lemma is the right canonical object anyway: Mathlib's `measurable_iInf`
requires a *countable* index, and the whole content here is that continuity in the parameter
replaces countability over an uncountable compact set.

**The three `tendstoInMeasure_*` rate lemmas — KEEP, unchanged.** Mathlib's
`ConvergenceInMeasure` offers entry points from a.e. convergence, from `eLpNorm`
convergence, and the `iff_dist`/`iff_norm`/`iff_enorm` reformulations — but **no**
vanishing-rate or high-probability entry point at all. These three are the
concentration-inequality bridge and fill a real gap. The names are already
conclusion-first, and the review risk this section listed ("proof-specific rate lemmas") does
not hold: they are stated over an arbitrary filter `l` and an arbitrary `EDist E`, matching
the generality of `TendstoInMeasure` itself. The docstrings' claim that null-measurability is
dispensable for the first two but *not* for the third is correct and was re-derived: bounding
`μ bad` above from `μ good → 1` needs superadditivity, which fails for outer measures.

**`measurable_of_iUnion_restrict` — KEEP.** `exact?` cannot close it; upstream has only the
two-set `measurable_of_restrict_of_restrict_compl`, not the countable-cover version.

**COUPLING, recorded for every future rename lane.** These declarations are restated verbatim
in `Challenge/MathlibPending/{CfcMeasurable,TendstoInMeasure,ProbabilityQoL}/{Conformance,Leaderboard}.lean`
and listed by name in three `comparator/*.json` configs, with live consumers in
`Acharyya2024/WellKnown.lean` and `DkpsQuench2026/Paper/EvaluationConcentration.lean`.
`Challenge` is **not** in `defaultTargets`. This pass therefore renamed nothing — the audit
found no rename worth the churn — and all five §10 `Challenge` modules were built
individually to confirm.

## 11. Haagerup-Zsido kernel decomposition — RESOLVED

The 1673-line monolith was split into 7 topic modules (commit `f35ffc0`:
`ExponentialAbs`, `Poisson/CauchyLattice`, `SpecialFunctions/Integral/{RationalQuadratic,SineLaplace}`,
`HaagerupZsido/{Defs,Integrability,Fourier}`; old path is a thin re-export) and
polished for review (commits `72b4697` renames, `df963aa` generic relocation,
`e5fd786` privatization + dead-hypothesis removal, `d5074a9` import trim,
`5ad1b91` `weight_def`). All files < 1000 lines; 26 intermediates privatized;
`innerLaplace`→`weightLaplaceTransform`, `weight_mul_expRatio`→`weight_mul_exp_ratio`;
`integrable_of_even_integrableOn_Ioi`→`MeasureTheory.integrable_iff_integrableOn_Ioi_of_even`,
`abs_sin_abs`/`abs_sin_add_nat_mul_pi`→`Real` namespace. The per-declaration tables
are removed from the backlog so they are not re-treaded. Remaining optional follow-up
(not blocking): full de-`@[expose]` of bodies, and per-file explicit direct Mathlib
imports for self-containment.

## 12. Next-wave convergence signatures

These sections are representation work, not a cosmetic-renaming backlog. When a
canonical Tau Ceti/Mathlib representation is already forced, the corresponding
section becomes an executable migration lane immediately. **Section 12.2 is now
active and claimed**; Sections 12.3–12.7 remain design-stage until their own
canonical representation decisions are closed.

### 12.1 ~~Rectangular symmetric ideal families~~ — P0 RESOLVED 2026-07-27

The extensionality defect is fixed. `ForTauCeti/Analysis/OperatorIdeal/Family/Basic.lean` carries the canonical replacement:

```lean
structure OperatorIdealFamily (𝕜) [NontriviallyNormedField 𝕜] where
  gauge : ∀ {E : Type v} {F : Type w} [...], (E →L[𝕜] F) → ℝ≥0∞
  gauge_add_le  ...      -- four laws, all unconditional
  gauge_smul    ...
  enorm_le_gauge ...
  gauge_comp_le ...

structure SymmetricOperatorIdealFamily (𝕜) [RCLike 𝕜]
    extends OperatorIdealFamily.{u, v, v} 𝕜 where
  gauge_adjoint ...
```

What was executed, against each bullet of the original TODO:

- *"Replace Mem plus gauge with a subtype element whose norm is the ideal norm."* Done, with one refinement that turned out to matter more: the **data** is a single total gauge into `ℝ≥0∞`, and the ideal `OperatorIdealFamily.carrier : Submodule 𝕜 (E →L[𝕜] F)` is *derived* as its finiteness domain. This is strictly better than a `(carrier, norm-on-carrier)` pair, because a pair still needs a coherence axiom between the two fields and still admits two records with the same carrier and norm but different bundled instances. A single field has `ext` for free, and the "gauge = ∞ off the ideal" convention is the classical Gohberg–Krein/Calkin one. The subtype-with-ideal-norm still exists, as the *derived* `OperatorIdealFamily.Elem` (a type synonym — the bare subtype already inherits the operator norm, and the two differ).

- *"Express zero/add/smul/completeness through standard typeclasses."* Done. Closure under `0`, `+`, `•`, `-`, finite sums is `Submodule` membership; the ideal norm is a real `NormedAddCommGroup`/`NormedSpace` on `Elem`; completeness is the mixin `OperatorIdealFamily.IsComplete`, i.e. `CompleteSpace (N.Elem E F)` (with `[CompleteSpace F]`, exactly as for the ambient `E →L[𝕜] F`), replacing the hand-rolled ε–N `gauge_complete`.

- *"Allow independent source and target universes."* Done for the base layer, **with a recorded obstruction**: the adjoint exchanges source and target, so a family closed under adjoints cannot keep them independent. Hence the split — `OperatorIdealFamily` over Banach spaces with universes `v`, `w`, and `SymmetricOperatorIdealFamily` extending its *diagonal* instantiation over Hilbert spaces. One structure with an optional adjoint field is not expressible.

- *"Split the minimal normed operator ideal, symmetric structure, and Ky Fan dominance into layered classes."* First two layers done as above; Ky Fan dominance remains for Layer C.2 of the approximation-number roadmap and should be a mixin over `SymmetricOperatorIdealFamily`, not a fourteenth field.

- *"Provide extensionality."* `OperatorIdealFamily.ext`: equal gauges ⟹ equal families.

- *"Do not include Davis–Kahan-specific paper-norm normalization."* The generic structure has no normalization field. Note that `Φ(e₀) = 1`-style normalization belongs to the *symmetric-gauge* construction (roadmap C.1), not to the ideal-family interface.

Axiom count went 14 fields → 4 laws: `gauge 0 = 0` follows from homogeneity at `c = 0` (which also excludes the everywhere-`∞` gauge), definiteness from `‖A‖ₑ ≤ gauge A`, and every closure property from the carrier submodule.

**Validation and migration.** `DavisKahan/Interop/TauCeti/RectangularFamilyAdapter.lean` derives the entire historical record from the canonical one (`SymmetricOperatorIdealFamily.toRectangular`), including `gauge_complete`, so nothing the ~70 production consumers rely on was lost. There is deliberately no inverse — a historical record does not determine a canonical family, which *is* the defect. Remaining work is the incremental migration of those consumers, after which both the adapter and `RectangularSymmetricIdealFamily` are deleted. `KyFanDominantIdealFamily` (in `ApproximationNumbers.lean`) has the same free-data shape and should be redone as a mixin during that migration.

### 12.2 Closed and self-adjoint unbounded operators — P0 ACTIVE / CLAIMED

> **Decision closed:** the canonical foundational object is Mathlib
> `LinearPMap`, with closedness, density, symmetry, and self-adjointness as
> properties. The DKPS `ClosedOperator` bundle is a temporary downstream adapter,
> not an upstream candidate. See `dev/tauceti/u1-linearpmap-migration.md`.

Do not add a second definition when pinned Mathlib already supplies the notion.
The intended API shape is:

```lean
namespace LinearPMap

-- Reuse existing Mathlib predicates and add only missing characteristic lemmas.
-- Typical arguments are the partial map plus explicit facts:
variable (A : E →ₗ.[𝕜] F)
variable (hAclosed : A.IsClosed)
variable (hAdense : Dense (A.domain : Set E))

-- Domain-aware relations are predicates over partial maps, not new operator bundles.
def SameDomain (A B : E →ₗ.[𝕜] F) : Prop := A.domain = B.domain

def MapsDomainTo (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F)
    (X : E →L[𝕜] F) : Prop :=
  ∀ x : A.domain, X x.1 ∈ B.domain

end LinearPMap
```

Required implementation order:

1. **Inventory and exact correspondence.** Map every public declaration in
   `DavisKahan/SpectralTheory/ClosedOperator/Basic.lean` to an existing Mathlib /
   Tau Ceti declaration, a missing reusable `LinearPMap` theorem, a temporary
   adapter field, or a Davis--Kahan-specific downstream theorem.
2. **Canonical reusable core.** State same-domain, extension, domain transport,
   bounded extension, graph norm, relative boundedness, bounded embedding, and
   bounded-perturbation facts directly over `LinearPMap` in a dependency-clean
   `ForTauCeti` module tree.
3. **Compatibility seam.** Implement the historical bundle from the canonical
   layer under `DavisKahan/Interop/TauCeti/`; do not let it flow back into
   `ForTauCeti`.
4. **Consumer migration.** Repoint reducing restrictions, closed Sylvester
   equations, unbounded estimates, and graph/Riccati inputs in dependency order.
5. **Deletion/demotion.** Remove generic production imports of the historical
   bundle; retain only source-facing compatibility corollaries that have a real
   paper-interface purpose.

Hard requirements:

- derive density, symmetry, and closedness from self-adjointness where available
  rather than store redundant evidence;
- use equality of `LinearPMap.domain` or a simple predicate instead of a bundled
  `SameDomain` record unless additional data is genuinely required;
- represent bounded operators through Mathlib's existing full-domain partial-map
  constructor, not a second closed-operator embedding;
- define graph norm and bounded-extension constructions on the domain subtype of
  a `LinearPMap`;
- preserve green builds with adapters, but never treat adapter-backed greenness
  as completion;
- do not wait for Spectra PVM, real-spectrum, or complexification work; isolate
  those bridges downstream and continue the representation migration around them.

Exit criterion: no generic production theorem has DKPS `ClosedOperator` as its
fundamental input. A remaining use must be explicitly classified as a temporary
interop wrapper or a source-facing compatibility theorem.

### 12.3 Partial isometries and polar decomposition

```lean
def IsPartialIsometry (u : E →L[𝕜] F) : Prop := ...

noncomputable def ContinuousLinearMap.polarPartialIsometry
    (A : E →L[𝕜] F) : E →L[𝕜] F

@[simp] theorem polarPartialIsometry_comp_modulus ...
theorem polarPartialIsometry_isPartialIsometry ...
theorem initialSpace_polarPartialIsometry ...
theorem finalSpace_polarPartialIsometry ...
theorem polarPartialIsometry_unique ...
```

- Decide whether the algebraic star-monoid predicate and operator-geometric predicate should share one name or be separate layers.

- Generalize from finite-dimensional LinearMap to ContinuousLinearMap on Hilbert spaces where kernels/ranges are closed as needed.

- Define the canonical polar factor and characteristic API; do not expose only existence theorems.

- Use the same modulus definition as the approximation-number API.

- Port only missing Spectra range/kernel/support lemmas and preserve provenance.

### 12.4 Hilbert-Schmidt, trace class, and symmetric ideals

```lean
-- One canonical object/predicate, several equivalent characterizations.
def ContinuousLinearMap.IsHilbertSchmidt (T : E →L[𝕜] F) : Prop := ...
noncomputable def ContinuousLinearMap.hilbertSchmidtNorm (T : E →L[𝕜] F) : ℝ≥0 := ...

theorem isHilbertSchmidt_iff_summable_norm_apply_orthonormalBasis ...
theorem isHilbertSchmidt_iff_summable_sq_singularValue ...
theorem hilbertSchmidtNorm_eq_sqrt_tsum_norm_apply_sq ...
theorem hilbertSchmidtNorm_eq_frobeniusNorm ...
```

- Do not upstream independent tensor-based, column-based, and singular-value-based structures as peers.

- Choose one canonical predicate/norm and make all other presentations equivalence theorems.

- Settle scalar generality and rectangular maps before naming the files.

- Use the orthogonal-series module only as a prerequisite if its results are absent upstream.

- Port trace-class/Schatten material from Spectra after the Hilbert-Schmidt base is stable.

### 12.5 Sylvester equations and spectral separation

```lean
def sylvester (A : F →L[𝕜] F) (B : E →L[𝕜] E) :
    (E →L[𝕜] F) →L[𝕜] (E →L[𝕜] F) := ...

-- Natural properties, not paper vocabulary:
def SpectraSeparated (A B) (δ : ℝ) : Prop := ...

theorem sylvester_injective_of_spectraSeparated ...
theorem norm_le_inv_gap_mul_norm_sylvester ...
theorem existsUnique_sylvester_eq_of_spectraSeparated ...
```

- Remove Genuine, paper section numbers, and interval-specific names from generic predicates.

- Prefer set-distance or ordered spectral separation predicates that compose and specialize cleanly.

- Separate algebraic uniqueness, bounded inverse, and explicit integral/resolvent solution theorems.

- Use LinearPMap versions only after the unbounded-operator convergence refactor.

- Keep Davis-Kahan AX-XB=C wrappers downstream.

### 12.6 Projection geometry, directed angles, and graph subspaces

```lean
def directedGap (P Q : Submodule 𝕜 H) : ℝ := ‖Qᗮ.starProjection.comp P.subtypeL‖

def IsTransverseTo (Z V : Submodule 𝕜 H) : Prop := ...

noncomputable def graphOperator ...
noncomputable def tangentOperator ...

theorem approximationNumber_tangentOperator ...
```

- Keep directed and symmetric notions separate in names and types; never derive IsAcute from a one-way dimension embedding.

- Use projection/restriction maps with explicit source and target spaces rather than ambient square operators when ranks differ.

- Remove Θ/paper notation from generic theorem names; add paper aliases downstream.

- Define graph/tangent coordinates canonically and supply uniqueness/apply/range APIs.

- Reconcile with Tau Ceti/Spectra partial-isometry and spectral-projection structures before signatures freeze.

### 12.7 Spectra PVM and functional-calculus port

- Inventory only the declarations actually used by production Davis-Kahan modules.

- For each donor declaration, classify copied, generalized, specialized, or redesigned and retain exact provenance.

- Adopt Tau Ceti namespaces and LinearPMap/self-adjoint representation; do not preserve Spectra wrapper types solely to ease porting.

- Port definitions in dependency order: PVM basics, spectral projections, bounded Borel calculus, unbounded calculus/restriction, generator bridges.

- Give every definition an extensionality theorem, apply/composition API, and measurable/functional-calculus normalization lemmas before downstream migration.

- Keep historical source correspondence and Davis-Kahan-specific selectors downstream.

## 13. Definition-level deletion and adapter plan

*Reconciled 2026-07-27 against what has actually landed. Rows are struck through once the
canonical API exists; a struck-through row is not necessarily finished work — several still
carry a transitional adapter whose deletion condition is stated.*

| **Cluster** | **Current state** | **Signature risk** | **Upstream action** | **Priority** |
| --- | --- | --- | --- | --- |
| ~~operatorAbs~~ | **Canonical API landed (§7).** `ContinuousLinearMap.modulus` is the one rectangular modulus; `operatorAbs` survives only as a `reducible abbrev` in a documented not-for-upstream shim | Adapter is live, so the duplicate name is still importable | Delete the alias once its consumers move to `.modulus`; do not submit the alias | ~~P0~~ adapter-retirement |
| ClosedOperator | **ACTIVE / CLAIMED 2026-07-27.** Canonical representation fixed to `LinearPMap` + properties | Two competing closed-operator representations in production | Execute U1: build canonical core, adapter, consumer migration, then delete/demote bundle — see §12.2 | P0 |
| Spectra SelfAdjointOperator | **Open.** Still consumed across `DavisKahan/Sources/**` and `DavisKahan/Alternative/**` | Potential donor wrapper competing with the Tau Ceti representation | Port useful lemmas; choose canonical Tau Ceti representation | P1 |
| ~~specSubspace~~ | **Renamed (§6).** Canonical is `OrthonormalBasis.spanIndices` in `ForTauCeti/Analysis/InnerProductSpace/BasisSpan.lean`, generalized off `Fin`/predicates; `specSubspace` remains only inside `CourantFischerCompat.lean` | Compat shim is importable | Delete with the shim once the historical Courant–Fischer signatures are retired | ~~P0~~ adapter-retirement |
| ~~appendFin~~ | **Deleted (§8.1).** It was exactly `Fin.snoc`; `Fin.snoc_castSucc` / `Fin.snoc_last` replace its two simp lemmas | none | done — no adapter was needed | ~~P0~~ |
| **finiteMean** | **KEPT (§8.1) — the "likely generic duplicate" reading was wrong.** `Finset.expect` requires `Module ℚ≥0 E`, which does not synthesize for a general `𝕜`-inner-product space; `Finset.centroid` typechecks but is `Classical.arbitrary` junk on the empty family, whereas `finiteMean` returns `0` there and `finiteMean_append` is deliberately stated to hold *at* `n = 0` | none — it is not a duplicate | Keep. Open sub-item: generalize `Fin n` → `Finset`, which is a redesign of the add-one identity, not a signature edit | P2 (was P0) |
| ~~RectangularSymmetricIdealFamily~~ | **Replaced (§12.1).** `TauCeti.SymmetricOperatorIdealFamily` | Legacy record still has 68 consumers | `SymmetricOperatorIdealFamily.toRectangular` (transitional; delete with the legacy structure) | ~~P0~~ adapter-retirement |
| GenuinePairwiseSpectrumGap | **Open.** Still live across `DavisKahan/Sources/DavisKahan1970/**`, with `PairwiseSpectrumGap` aliased to it | Paper/bridge terminology in a generic position | Replace with canonical separation predicate | P1 |

- Adapters must be visibly downstream and carry a deletion condition.

- No adapter should be submitted to Tau Ceti merely to preserve DKPS source compatibility.

- After each canonical API lands, repoint consumers, remove duplicate declarations, and run a grep gate for old fully qualified names.

- Avoid long-lived aliases before upstream review; they obscure which API reviewers are evaluating.

> **Three adapters are now live at once** — `operatorAbs`, `CourantFischerCompat`, and
> `SymmetricOperatorIdealFamily.toRectangular` — which is exactly the "long-lived aliases
> obscure which API reviewers are evaluating" risk this section warns about. Retiring them is
> a distinct piece of work from the canonical-API lanes that created them, and it is not
> currently claimed by anyone.

> **~~Gate gap found while reconciling this table (§10 lane).~~ CLOSED 2026-07-27 —
> `scripts/check_declaration_name_drift.py`.** The last bullet above asks for "a grep gate for
> old fully qualified names" after each rename. There was no such gate, and its absence was
> not theoretical: the §9.2 rename passed a green 9272-job default build and still broke
> `Challenge.MathlibPending.RankPsdRealization.Leaderboard`, because `Challenge` is not in
> `defaultTargets` and `comparator/*.json` restates declaration names as data.
>
> The gate now exists and covers exactly those two blind spots. It is **build-free** — it
> resolves names by parsing declarations out of the sources rather than by asking Lean — so it
> runs in about a second and works on a tree that does not compile. Three hard checks:
> `pinned-name-resolves` (every name asserted as data, in a comparator `theorem_names` list or
> a `#print axioms` line, names a declaration that exists), `pinned-name-in-challenge` (the
> challenge module actually declares what its config pins — this is the
> `ForMathlib`-vs-`TauCeti` mismatch class, which compiles on both sides and fails only in the
> comparator's export comparison), and `pinned-name-unaudited` (a pinned statement whose axiom
> footprint no leaderboard certifies). A leaderboard auditing *more* than its config pins is
> reported as an informational note, not a failure — that is legitimate.
>
> **Limits, stated rather than hidden:** resolution is syntactic, so it does not follow
> `export`, `open … in`, or alias targets, and a pass is not proof of resolvability. It is a
> tripwire for the failure mode that has actually occurred here; the compiler and
> `scripts/check_comparator_signatures.py` remain ground truth. Regression tests in
> `scripts/tests/test_check_declaration_name_drift.py` pin the two bugs found while writing it
> — a bare `end` closing a `section` must not pop a `namespace`, and the `end`/`namespace`/
> `section` patterns must not span newlines (`\s*$` under `re.MULTILINE` parses `end` and a
> following `section` as one `end section`, silently unbalancing every name in the file).

## 14. Pre-PR declaration checklist

- [ ] Roadmap target names this mathematical product or a necessary prerequisite.

- [ ] Exact-name and semantic grep found no direct Mathlib/Tau Ceti replacement.

- [ ] Any nearby partial replacement is reused and cited in the PR rationale.

- [ ] The declaration is at the natural scalar, universe, dimensional, and completeness generality.

- [ ] No assumption is unused or merely inherited from a broad section variable block.

- [ ] The outer quantifier and statement strength agree with the theorem name.

- [ ] The name describes the conclusion in terminology already used nearby.

- [ ] The namespace is the object being extended, not TauCeti by default.

- [ ] The file is the earliest canonical home consistent with dependencies.

- [ ] Definition bodies are hidden unless computation genuinely requires exposure.

- [ ] Each definition has a _def/iff/ext/apply/operation API sufficient to avoid unfolding.

- [ ] Normal-form lemmas have tested simp/grind annotations; no gratuitous attributes.

- [ ] Proof-only helpers are private.

- [ ] Symmetric/dual forms are added only when needed or already developed.

- [ ] Public conclusions do not expose constructor proof terms or conversion noise.

- [ ] Indexing, normalization, Fourier convention, and zero-padding semantics are explicit.

- [ ] Donor provenance identifies repository, commit, path, declaration, license, and semantic changes.

- [ ] The PR contains one topic and no unrelated generic helper unless that helper is a prerequisite extracted first.

- [ ] Downstream Davis-Kahan builds against the proposed API without unfolding or source-facade imports.

- [ ] The old parallel API has a concrete deletion plan.

## Appendix A. Name-change index

| **Current** | **Candidate** | **Decision status** |
| --- | --- | --- |
| approximationNumber_def | approximationNumber_eq_iInf | **Done 2026-07-27** (also de-simped) |
| approximationNumber_le | ~~approximationNumber_le_nnnorm_sub~~ → **approximationNumber_le_norm_sub** | **Done 2026-07-27**; `nnnorm` in the sketch is stale — the codomain decision (2) made the API real-valued, so the suffix is `norm`, not `nnnorm`. The same correction applies to every `_nnnorm_` sketch below. |
| approximationNumber_eq | ~~approximationNumber_eq_nnnorm_sub_of_isLeast~~ → **approximationNumber_eq_norm_sub_of_forall_le** | **Done 2026-07-27** (§5.1); the `IsLeast` packaging was declined — it forces call sites to build and destructure the set of admissible distances |
| lt_approximationNumber_add_pos | **exists_rank_le_norm_sub_lt_approximationNumber_add** | **Done 2026-07-27** (§5.1); `nnnorm` → `norm` per the codomain decision. Kept public: consumers in another file |
| approximationNumber_add_le | **approximationNumber_add_le_add_norm** | **Done 2026-07-27** (§5.1); paired with the row below. `norm_add_le` is the precedent that decides which of the two additive theorems keeps the short name |
| approximationNumber_add_le_add | **approximationNumber_add_le** | **Done 2026-07-27** (§5.1); the principal additive ideal inequality now carries the canonical short name |
| approximationNumber_zero | **approximationNumber_index_zero** | **Done 2026-07-27** (§5.1); the plain `_zero` suffix belongs to the zero *operator*, per `LinearMap.singularValues_zero` / `opNorm_zero` / `rank_zero`. The index is named by its role, as in `eLpNorm_exponent_zero` |
| zero_approximationNumber | **approximationNumber_zero** | **Done 2026-07-27** (§5.1); head symbol leads. The sketched `approximationNumber_zero_map` was declined — `_map` is not a Mathlib suffix |
| antitone_approximationNumber | **approximationNumber_antitone** | **Done 2026-07-27** (§5.1); matches `LinearMap.singularValues_antitone` on the object this one is proved equal to, and enables dot notation |
| approximationNumber_comp_right_le | **approximationNumber_comp_le_mul_norm** | **Done 2026-07-27** (§5.1); conclusion-oriented, `∘L` kept to match `opNorm_comp_le` |
| approximationNumber_comp_left_le | **approximationNumber_comp_le_norm_mul** | **Done 2026-07-27** (§5.1); parallel to the row above, differing exactly where the statements differ |
| rank_comp_left_le_of_rank_le | **LinearMap.rank_comp_le_natCast_right** (+ two `ContinuousLinearMap` specializations) | **Done 2026-07-27** (§5.1); moved to `ForTauCeti/LinearAlgebra/Dimension/RankComp.lean` and generalized off continuous maps. Privatizing was impossible — four independent consumers |
| singularValues_le_norm_sub_of_rank_le | singularValue_le_norm_sub_of_rank_le | Sketch; verify adjacent Mathlib naming |
| approximationNumber_eq_singularValues | approximationNumber_eq_singularValue | Sketch; verify adjacent Mathlib naming |
| lowerBound_le_approximationNumber_of_finrank | le_approximationNumber_of_finrank_lt | Sketch; verify adjacent Mathlib naming |
| specSubspace | OrthonormalBasis.spanIndices | Sketch; verify adjacent Mathlib naming |
| forall_unit_vector_eigenvalue_le_re_inner | exists_submodule_forall_unit_eigenvalue_le_re_inner | Sketch; verify adjacent Mathlib naming |
| abs_eigenvalues_sub_le_opNorm | abs_eigenvalue_sub_eigenvalue_le_norm | Sketch; verify adjacent Mathlib naming |
| eigenvalues_le_eigenvalues_of_re_inner_le | eigenvalue_mono | Sketch; verify adjacent Mathlib naming |
| rectangularOperatorModulus | ContinuousLinearMap.modulus | Sketch; verify adjacent Mathlib naming |
| operatorAbs | delete; square specialization of modulus | Sketch; verify adjacent Mathlib naming |
| finiteMean | *(no rename)* | **KEPT 2026-07-27** (§8.1) — not a duplicate: `Finset.expect` needs `Module ℚ≥0 E`, which does not synthesize here; `Finset.centroid` is affine with `Classical.arbitrary` empty-family junk |
| centeredScatter | *(name kept)* | **RETYPED 2026-07-27** (§8.1) to `E →L[𝕜] E`; `scatterOperator` was rejected because it states the normalization no better |
| appendFin | `Fin.snoc` | **DELETED 2026-07-27** (§8.1) — it was exactly `Fin.snoc`; note the two are *not* `rfl`-equal, `snoc` transports along `cast` |
| PosSemidef.eigenvalues₀_eq_zero_of_le | Matrix.PosSemidef.eigenvalues₀_eq_zero_of_rank_le | **Landed 2026-07-27** (§9.2); `i` made implicit, and the two facts its proof buried are now separate exports |
| exists_two_sided_inverse_of_spectrum_gap | isUnit_of_forall_le_abs + IsSelfAdjoint.norm_ringInverse_le | **Landed 2026-07-27** (§9.1); split, and invertibility dropped the `IsSelfAdjoint` hypothesis |
| norm_sq_finset_sum_of_pairwise_inner_eq_zero | norm_sum_sq_of_pairwise_inner_eq_zero | **Landed 2026-07-27** (§8.3); `finset` dropped as redundant. The other names in that file deliberately keep `_of_pairwise_inner_eq_zero`, mirroring upstream `OrthogonalFamily.*` — there is no bundled Mathlib predicate for pairwise-orthogonal *vectors* |
| norm_sq_sdiff_sum_of_pairwise_inner_eq_zero | *(deleted)* | **DELETED 2026-07-27** (§8.3) — subsumed by `OrthogonalFamily.norm_sq_sdiff_sum` and left unused once the Cauchy argument was replaced; the backlog had proposed only privatizing it |
| *(new)* | orthogonalFamily_of_pairwise_inner_eq_zero | **Added 2026-07-27** (§8.3) — the constructor Mathlib lacks: `Orthonormal.orthogonalFamily` requires *unit* vectors, so nothing covered a merely pairwise-orthogonal family |
| IsSelfAdjoint.norm_le_of_spectrum_subset_Icc | IsSelfAdjoint.norm_le_iff_spectrum_subset_Icc | **Landed 2026-07-27** (§9.1); strengthened to an iff, one-directional form not retained |

## Appendix B. Review questions to answer in roadmaps

1. Which approximation-number index convention is canonical for Tau Ceti, and why?

1. Should approximation numbers be ℝ-valued or ℝ≥0-valued?

1. Should the definition extend ContinuousLinearMap or live under TauCeti?

1. What is the canonical name for the source modulus of a rectangular operator?

1. Which existing Mathlib CFC square-root declarations make modulus lemmas redundant?

1. What exact Courant-Fischer equality is the roadmap product, rather than merely a support lemma?

1. ~~Does Tau Ceti want a bundled SelfAdjointOperator, or properties on LinearPMap?~~ **Resolved 2026-07-27:** `LinearPMap` plus properties is canonical; a thin bundle is permitted only as a derived convenience after the property API exists.

1. What is the minimal PVM/Borel-calculus slice to port from Spectra?

1. What single Hilbert-Schmidt predicate and norm will tensor, column, and singular-value characterizations share?

1. How should a symmetric operator ideal be represented so equality/extensionality ignores nonmembers?

1. Which generic Haagerup-Zsido prerequisites belong in Mathlib-like files, and which should remain private?

1. Which downstream paper aliases are explicitly excluded from Tau Ceti?

## Source basis

Repository audit: aiq-dkps-formalization archive 543b46f42573, including ForTauCeti, ForMathlib, DavisKahan, external/TauCeti, and dev/tauceti planning files.

Review criteria: TauCetiProject/TauCeti AGENTS.md and TauCetiProject/TauCetiReview rubrics at review commit b9539a39556d34b3e3bf6199d0da7b4e7d5d4c27 (correctness, reuse, scope, attribution, API design, generality, placement, naming, documentation, proof quality).

Internal polishing guidance: dev/mathlib-proof-polishing.md and dev/mathlib-quality-adapter.md.
