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

6. Courant-Fischer and finite spectral API

7. Operator modulus and absolute value convergence

8. Inner-product-space utilities

9. C*-algebra and matrix helpers

10. Measure-theory helpers

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
| Approximation numbers | Staged and Mathlib-only | Indexing, codomain, characteristic API | Settle representation; split into small PRs | P0 |
| Courant-Fischer | Staged helper layer | Misleading specSubspace and missing min-max endpoint | Refactor around basis spans and actual min-max theorem | P0 |
| Operator modulus / operatorAbs | Two overlapping APIs | Duplicate definitions and noncanonical names | Unify into one modulus API | P0 |
| Near isometry | Staged real finite-dimensional result | Existential instead of canonical polar factor; wrong generality split | Define canonical object; derive finite equiv | P0 |
| Centered scatter | Staged | Custom finite mean and append family | Refactor to Finset/Fintype and reuse average/cons | P1 |
| Orthogonal series | Staged | Likely duplicate helpers; proof-shaped names | Reuse Orthogonal predicate and existing summability API | P1 |
| Haagerup-Zsido kernel | Staged monolith, 1673 lines | File size, public helper explosion, generic lemmas mixed in | Split into 7-8 modules; privatize/move helpers | P0 |
| Closed operators / semigroups | Production local API | Parallel to Tau Ceti LinearPMap architecture | Rewrite over LinearPMap properties | P0 |
| Symmetric ideal families | Production local structure | Unconstrained gauge off carrier; fixed universes | Redesign as normed subtype/family | P0 |
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

1. PR U1: LinearPMap convergence refactor for closed/self-adjoint operators; no new perturbation theorem.

1. PR S1+: dependency-closed Spectra ports with exact provenance, after reuse audit.

1. Independent utility PRs: centered scatter, orthogonal series, measure-theory criteria, only if roadmapped and reuse-clean.

1. Haagerup-Zsido series: split prerequisite analytic lemmas from the final kernel theorem; no 1673-line PR.

## 5. Approximation-number foundation

### 5.1 Basic.lean

| **Current file** | ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Basic.lean |
| --- | --- |
| **Proposed disposition** | Keep the mathematics; redesign the convention/API before upstreaming. |
| **Readiness** | Medium. Proofs are mature, but the representation decision affects every later theorem. |
| **Primary review risks** | Zero-based rank convention; NNReal versus Real; global namespace extension; overexposed body; vague characteristic theorem names. |
| **Likely PR slice** | PR A1 after roadmap acceptance. |

> **P0 convention decision**
>
> Choose and document one convention: current aₙ(T) is the distance to maps of rank at most n, so a₀(T)=‖T‖. This is coherent but differs from the common one-based rank < n convention. The roadmap must explicitly approve the zero-based convention, or the entire API should be reindexed before any PR.

> **P0 codomain decision**
>
> Decide whether approximationNumber returns ℝ≥0 or ℝ. NNReal makes positivity and norm bounds pleasant but creates constructor noise when compared with Mathlib singularValues : ℝ. A likely Mathlib-style alternative is a real-valued definition plus approximationNumber_nonneg, with an optional NNReal accessor. Do not carry both full APIs.

#### P0  le_natCast_of_lift_le

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

#### P0  approximationNumber

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

#### P1  approximationNumber_def

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

#### P1  approximationNumber_le

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

#### P1  le_approximationNumber

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

#### P1  approximationNumber_eq

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

#### P1  approximationNumber_zero

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

#### P2  antitone_approximationNumber

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

#### P2  approximationNumber_le_nnnorm

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

#### P2  zero_approximationNumber

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

#### P1  approximationNumber_nonneg

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

#### P1  lt_approximationNumber_add_pos

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

#### P1  approximationNumber_add_le

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

#### P1  approximationNumber_add_le_add

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

#### P0  rank_comp_left_le_of_rank_le

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

#### P1  approximationNumber_comp_right_le

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

#### P1  approximationNumber_comp_left_le

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

#### P2  approximationNumber_comp_comp_le

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

#### P2  approximationNumber_smul

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

#### P0  singularValues_le_norm_sub_of_rank_le

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

#### P0  singularValues_le_approximationNumber

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

#### P0  approximationNumber_eq_singularValues

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

#### P0  lowerBound_le_approximationNumber_of_finrank

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

#### P1  lowerBound_le_approximationNumber_of_linearIndependent

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

## 7. Operator modulus and absolute value convergence

> **P0 duplicate API**
>
> ForTauCeti currently contains rectangularOperatorModulus while a separate staged OperatorAbsoluteValue file defines operatorAbs for square maps. These are the same construction at different generalities. Upstreaming both would create a parallel API and likely trigger the reuse rubric. Keep one rectangular source-modulus definition and derive the square specialization.

| **Current file** | OperatorModulus.lean + OperatorAbsoluteValue.lean |
| --- | --- |
| **Proposed disposition** | Merge into one canonical ContinuousLinearMap modulus API. |
| **Readiness** | Low until naming and namespace are settled. |
| **Primary review risks** | Duplicate definitions; rectangular prefix is proof-history terminology; square multiplication versus composition; complex-only assumptions. |
| **Likely PR slice** | PR A4, separate prerequisite refactor. |

#### P0  rectangularOperatorModulus

**Disposition: Unify definition**

```lean
noncomputable def rectangularOperatorModulus (T : E →L[ℂ] F) : E →L[ℂ] E
```

**Proposed target shape**

```lean
noncomputable def ContinuousLinearMap.modulus
    (T : E →L[ℂ] F) : E →L[ℂ] E :=
  CFC.sqrt (T.adjoint.comp T)
```

- Use the general rectangular map as the sole definition.

- The source space already disambiguates the construction; rectangular in every name is unnecessary.

- Evaluate whether Mathlib convention prefers abs, modulus, or operatorAbs; search adjacent C*-algebra names before choosing.

- Expose a square specialization theorem rather than a second definition.

**Likely adversarial review:** Two public definitions for the same mathematical object are a reuse/API blocker.

#### P1  rectangularGram_nonneg

**Disposition: Merge family**

```lean
theorem rectangularGram_nonneg (T : E →L[ℂ] F) : 0 ≤ T.adjoint ∘L T
```

**Proposed target shape**

```lean
theorem ContinuousLinearMap.adjoint_comp_self_nonneg (T) : 0 ≤ T.adjoint.comp T
```

- Rename under the single modulus API.

- Delete the corresponding operatorAbs duplicate where present.

**Likely adversarial review:** The name rectangularGram is local terminology and may duplicate an existing positivity theorem.

#### P1  rectangularOperatorModulus_nonneg

**Disposition: Merge family**

```lean
theorem rectangularOperatorModulus_nonneg (T : E →L[ℂ] F) : 0 ≤ rectangularOperatorModulus T
```

**Proposed target shape**

```lean
theorem ContinuousLinearMap.modulus_nonneg (T) : 0 ≤ T.modulus
```

- Rename under the single modulus API.

- Delete the corresponding operatorAbs duplicate where present.

**Likely adversarial review:** Characteristic result; should live by the definition and likely feed self-adjointness.

#### P1  isSelfAdjoint_rectangularOperatorModulus

**Disposition: Merge family**

```lean
theorem isSelfAdjoint_rectangularOperatorModulus (T : E →L[ℂ] F) : IsSelfAdjoint (rectangularOperatorModulus T)
```

**Proposed target shape**

```lean
theorem ContinuousLinearMap.modulus_isSelfAdjoint (T) : IsSelfAdjoint T.modulus
```

- Rename under the single modulus API.

- Delete the corresponding operatorAbs duplicate where present.

**Likely adversarial review:** Current name order is inconsistent with method-style API.

#### P1  rectangularOperatorModulus_mul_self

**Disposition: Merge family**

```lean
theorem rectangularOperatorModulus_mul_self (T : E →L[ℂ] F) : rectangularOperatorModulus T * rectangularOperatorModulus T = T.adjoint ∘L T
```

**Proposed target shape**

```lean
theorem ContinuousLinearMap.modulus_sq (T) : T.modulus * T.modulus = T.adjoint.comp T
```

- Rename under the single modulus API.

- Delete the corresponding operatorAbs duplicate where present.

**Likely adversarial review:** Use a standard sq/mul_self naming precedent and canonical composition.

#### P1  norm_rectangularOperatorModulus_apply

**Disposition: Merge family**

```lean
theorem norm_rectangularOperatorModulus_apply (T : E →L[ℂ] F) (x : E) : ‖rectangularOperatorModulus T x‖ = ‖T x‖
```

**Proposed target shape**

```lean
@[simp] theorem ContinuousLinearMap.norm_modulus_apply (T) (x) : ‖T.modulus x‖ = ‖T x‖
```

- Rename under the single modulus API.

- Delete the corresponding operatorAbs duplicate where present.

**Likely adversarial review:** This is the key computation theorem and should likely be simp.

#### P1  norm_rectangularOperatorModulus

**Disposition: Merge family**

```lean
theorem norm_rectangularOperatorModulus (T : E →L[ℂ] F) : ‖rectangularOperatorModulus T‖ = ‖T‖
```

**Proposed target shape**

```lean
@[simp] theorem ContinuousLinearMap.norm_modulus (T) : ‖T.modulus‖ = ‖T‖
```

- Rename under the single modulus API.

- Delete the corresponding operatorAbs duplicate where present.

**Likely adversarial review:** Low risk after the definition is canonical.

#### P1  operatorAbs_unique

**Disposition: Generalize / rename**

```lean
theorem operatorAbs_unique {T b : E →L[ℂ] E} (hb : 0 ≤ b) (h : b * b = star T * T) : b = operatorAbs T
```

**Proposed target shape**

```lean
theorem ContinuousLinearMap.eq_modulus_of_nonneg_of_sq_eq
    (hb : 0 ≤ b) (hsq : b * b = T.adjoint * T) :
    b = T.modulus
```

- Keep uniqueness as a characterization theorem for the one modulus definition.

- State it in the general source-space setting if CFC uniqueness supports it.

- Name from the equality conclusion and hypotheses; avoid operatorAbs after unification.

**Likely adversarial review:** This is useful API, but only after the duplicate definition is removed.

#### P2  operatorAbs_commute_operatorAbs

**Disposition: Reuse judgment**

```lean
theorem operatorAbs_commute_operatorAbs {S T : E →L[ℂ] E} (h : Commute (star S * S) (star T * T)) : Commute (operatorAbs S) (operatorAbs T)
```

**Proposed target shape**

```lean
theorem ContinuousLinearMap.modulus_commute_modulus
    (h : Commute (S.adjoint * S) (T.adjoint * T)) :
    Commute S.modulus T.modulus
```

- Check whether CFC already has a commute-map theorem making this one line.

- Consider a more general CFC sqrt commute theorem rather than an operator-specific restatement.

- Keep only if downstream operator-theory users need this specialization.

**Likely adversarial review:** Reuse review may identify this as a direct CFC corollary that does not need a public specialized theorem.

#### P1  norm_operatorAbs_mul

**Disposition: Audit and generalize**

```lean
theorem norm_operatorAbs_mul (S D : E →L[ℂ] E) : ‖operatorAbs S * D‖ = ‖S * D‖
```

**Proposed target shape**

```lean
theorem norm_modulus_mul (S D : E →L[ℂ] E) :
    ‖S.modulus * D‖ = ‖S * D‖
```

- Verify the mathematical orientation and whether this needs D to commute; the current theorem is nonobvious and deserves a precise docstring.

- Generalize rectangular source/target spaces if composition types permit.

- Name and place under the modulus namespace, not a duplicate square API.

**Likely adversarial review:** Correctness review will scrutinize a norm equality this strong; the docstring must explain the adjoint calculation.

#### P1  norm_mul_operatorAbs

**Disposition: Audit**

```lean
theorem norm_mul_operatorAbs (D T : E →L[ℂ] E) : ‖D * operatorAbs T‖ = ‖D * star T‖
```

**Proposed target shape**

```lean
theorem norm_mul_modulus (D T : E →L[ℂ] E) :
    ‖D * T.modulus‖ = ‖D * T.adjoint‖
```

- Check whether the right side should be D*T or D*T.adjoint and explain why.

- Generalize dimensions/types where possible.

- Avoid publishing both left/right forms unless both have consumers.

**Likely adversarial review:** The asymmetric right-hand side is surprising and likely to receive correctness and naming scrutiny.

## 8. Inner-product-space utilities

### 8.1 CenteredScatter.lean

| **Current file** | ForTauCeti/Analysis/InnerProductSpace/CenteredScatter.lean |
| --- | --- |
| **Proposed disposition** | Refactor around a finite set/type and existing averaging API; retain the Welford update identity. |
| **Readiness** | Medium-low. |
| **Primary review risks** | Custom finiteMean and appendFin duplicate general combinators; normalization is implicit; LinearMap versus ContinuousLinearMap. |
| **Likely PR slice** | Independent roadmap/PR after reuse audit. |

#### P0  finiteMean

**Disposition: Reuse / generalize**

```lean
noncomputable def finiteMean {n : ℕ} (z : Fin n → E) : E
```

**Proposed target shape**

```lean
noncomputable def Finset.mean
    (s : Finset ι) (z : ι → E) : E :=
  (s.card : 𝕜)⁻¹ • ∑ i ∈ s, z i
```

- Search Mathlib for average/centroid/expectation over a finite set before defining anything.

- Generalize from Fin n to Finset or Fintype; make empty-family behavior explicit.

- Do not use the generic name finiteMean in namespace TauCeti if the object is tied to a finite family.

**Likely adversarial review:** Reuse review is likely to find an existing finite average construction or request a general Finset API.

#### P0  appendFin

**Disposition: Delete / privatize**

```lean
def appendFin {n : ℕ} (z : Fin n → E) (y : E) : Fin (n + 1) → E
```

**Proposed target shape**

```lean
-- Delete in favor of Fin.cons, Matrix.vecCons, or an equivalence-based append.
-- Keep only private if no canonical combinator matches.
```

- Search for Fin.cons and existing vector append operations.

- The helper is implementation scaffolding for one update theorem, not a reusable public object.

- If retained, put it in a generic Fin utility file, not CenteredScatter.

**Likely adversarial review:** A public hand-rolled Fin append is a classic reuse-rubric target.

#### P0  centeredScatter

**Disposition: Redesign**

```lean
noncomputable def centeredScatter {n : ℕ} (z : Fin n → E) : E →ₗ[𝕜] E
```

**Proposed target shape**

```lean
noncomputable def scatterOperator
    (s : Finset ι) (z : ι → E) : E →L[𝕜] E :=
  ∑ i ∈ s, rankOne 𝕜 (z i - s.mean z) (z i - s.mean z)
```

- Choose scatterOperator versus covarianceOperator based on normalization; current definition is unnormalized.

- Prefer ContinuousLinearMap for an analytic operator with positivity/order/norm consumers.

- Generalize to finite types/Finsets and avoid a custom append encoding.

- Provide apply/inner/self-adjoint/nonneg API without unfolding.

**Likely adversarial review:** The current name is plausible, but the signature does not state normalization and uses a narrower indexing representation than necessary.

#### P1  sum_sub_finiteMean_eq_zero

**Disposition: Rename after refactor**

```lean
theorem sum_sub_finiteMean_eq_zero {n : ℕ} (z : Fin n → E) : ∑ i, (z i - finiteMean 𝕜 z) = 0
```

**Proposed target shape**

```lean
theorem sum_sub_mean_eq_zero ...
```

- Rewrite against the Finset/Fintype API and canonical mean.

- Use consistent apply/self/order terminology.

- Keep only the update and positivity results that have independent consumers.

**Likely adversarial review:** All current names depend on the local finiteMean/appendFin representation and should be revisited together.

#### P1  finiteMean_append

**Disposition: Rename after refactor**

```lean
theorem finiteMean_append {n : ℕ} (z : Fin n → E) (y : E) : finiteMean 𝕜 (appendFin z y) = finiteMean 𝕜 z + ((n : 𝕜) + 1)⁻¹ • (y - finiteMean 𝕜 z)
```

**Proposed target shape**

```lean
theorem mean_cons ...
```

- Rewrite against the Finset/Fintype API and canonical mean.

- Use consistent apply/self/order terminology.

- Keep only the update and positivity results that have independent consumers.

**Likely adversarial review:** All current names depend on the local finiteMean/appendFin representation and should be revisited together.

#### P1  centeredScatter_append

**Disposition: Rename after refactor**

```lean
theorem centeredScatter_append {n : ℕ} (z : Fin n → E) (y : E) : centeredScatter 𝕜 (appendFin z y) = centeredScatter 𝕜 z + ((n : 𝕜) / ((n : 𝕜) + 1)) • (rankOne 𝕜 (y - finiteMean 𝕜 z) (y - finiteMean 𝕜 z)).toLinearMap
```

**Proposed target shape**

```lean
theorem scatterOperator_cons ...
```

- Rewrite against the Finset/Fintype API and canonical mean.

- Use consistent apply/self/order terminology.

- Keep only the update and positivity results that have independent consumers.

**Likely adversarial review:** All current names depend on the local finiteMean/appendFin representation and should be revisited together.

#### P1  re_inner_centeredScatter_self

**Disposition: Rename after refactor**

```lean
theorem re_inner_centeredScatter_self {n : ℕ} (z : Fin n → E) (x : E) : RCLike.re (inner 𝕜 (centeredScatter 𝕜 z x) x) = ∑ i, ‖inner 𝕜 (z i - finiteMean 𝕜 z) x‖ ^ 2
```

**Proposed target shape**

```lean
theorem re_inner_scatterOperator_apply_self ...
```

- Rewrite against the Finset/Fintype API and canonical mean.

- Use consistent apply/self/order terminology.

- Keep only the update and positivity results that have independent consumers.

**Likely adversarial review:** All current names depend on the local finiteMean/appendFin representation and should be revisited together.

#### P1  centeredScatter_isPositive

**Disposition: Rename after refactor**

```lean
theorem centeredScatter_isPositive {n : ℕ} (z : Fin n → E) : (centeredScatter 𝕜 z).IsPositive
```

**Proposed target shape**

```lean
theorem scatterOperator_isPositive ...
```

- Rewrite against the Finset/Fintype API and canonical mean.

- Use consistent apply/self/order terminology.

- Keep only the update and positivity results that have independent consumers.

**Likely adversarial review:** All current names depend on the local finiteMean/appendFin representation and should be revisited together.

#### P1  centeredScatter_le_append

**Disposition: Rename after refactor**

```lean
theorem centeredScatter_le_append {n : ℕ} (z : Fin n → E) (y : E) : centeredScatter 𝕜 z ≤ centeredScatter 𝕜 (appendFin z y)
```

**Proposed target shape**

```lean
theorem scatterOperator_le_scatterOperator_cons ...
```

- Rewrite against the Finset/Fintype API and canonical mean.

- Use consistent apply/self/order terminology.

- Keep only the update and positivity results that have independent consumers.

**Likely adversarial review:** All current names depend on the local finiteMean/appendFin representation and should be revisited together.

#### P1  re_inner_centeredScatter_append

**Disposition: Rename after refactor**

```lean
theorem re_inner_centeredScatter_append {n : ℕ} (z : Fin n → E) (y x : E) : RCLike.re (inner 𝕜 (centeredScatter 𝕜 (appendFin z y) x) x) = RCLike.re (inner 𝕜 (centeredScatter 𝕜 z x) x) + (n : ℝ) / ((n : ℝ) + 1) * ‖inner 𝕜 (y - finiteMean 𝕜 z) x‖ ^ 2
```

**Proposed target shape**

```lean
theorem re_inner_scatterOperator_cons_apply_self ...
```

- Rewrite against the Finset/Fintype API and canonical mean.

- Use consistent apply/self/order terminology.

- Keep only the update and positivity results that have independent consumers.

**Likely adversarial review:** All current names depend on the local finiteMean/appendFin representation and should be revisited together.

### 8.2 NearIsometry.lean

| **Current file** | ForTauCeti/Analysis/InnerProductSpace/NearIsometry.lean |
| --- | --- |
| **Proposed disposition** | Replace anonymous existence with a canonical polar/isometric factor API; separate general embedding from finite-dimensional equivalence. |
| **Readiness** | Low in current signature shape. |
| **Primary review risks** | Real-only specialization, duplicated LinearMap/ContinuousLinearMap theorem, existential witness, hidden surjectivity reason. |
| **Likely PR slice** | After polar-decomposition convergence. |

#### P1  abs_one_sub_inv_sqrt_le

**Disposition: Move / clarify**

```lean
theorem abs_one_sub_inv_sqrt_le {μ δ : ℝ} (hδ : δ ≤ 1 / 2) (hμ : |μ - 1| ≤ δ) : |1 - (Real.sqrt μ)⁻¹| ≤ δ
```

**Proposed target shape**

```lean
theorem abs_one_sub_inv_sqrt_le_of_abs_sub_one_le
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hμ : |μ - 1| ≤ δ) :
    |1 - (sqrt μ)⁻¹| ≤ δ
```

- Give δ nonnegativity explicitly instead of deriving it indirectly from hμ.

- Place this scalar lemma in Real.Sqrt or a dedicated elementary analysis file, not inside near-isometry operator theory.

- Search for an existing bound on inv_sqrt.

**Likely adversarial review:** The current premise hδ : δ ≤ 1/2 omits the natural 0 ≤ δ assumption and hides how positivity is obtained.

#### P0  exists_linearIsometryEquiv_norm_sub_le

**Disposition: Major redesign**

```lean
theorem exists_linearIsometryEquiv_norm_sub_le (M : E →L[ℝ] E) {δ : ℝ} (hδ : δ ≤ 1 / 2) (hM : ‖ContinuousLinearMap.adjoint M * M - 1‖ ≤ δ) : ∃ W : E ≃ₗᵢ[ℝ] E, ∀ x : E, ‖M x - W x‖ ≤ 2 * δ * ‖x‖
```

**Proposed target shape**

```lean
noncomputable def ContinuousLinearMap.polarIsometry (M : E →L[𝕜] F) : E →L[𝕜] F

theorem norm_sub_polarIsometry_apply_le
    (hM : ‖M.adjoint * M - 1‖ ≤ δ) :
    ‖M x - M.polarIsometry x‖ ≤ C δ * ‖x‖

-- finite-dimensional/surjective corollary:
theorem exists_linearIsometryEquiv_norm_sub_le ...
```

- First prove the natural general object: an isometric embedding/partial isometry from polar decomposition.

- Derive a LinearIsometryEquiv only with finite-dimensional equal-rank or explicit surjectivity.

- Avoid two public theorems with the same basename in LinearMap and ContinuousLinearMap unless that matches established namespaces.

- Generalize from ℝ to RCLike if the proof is not genuinely ordered-real-specific.

**Likely adversarial review:** Generality and API reviewers will ask why a canonical polar factor is returned only existentially and why the theorem is duplicated at two operator levels.

### 8.3 OrthogonalSeries.lean

| **Current file** | ForTauCeti/Analysis/InnerProductSpace/OrthogonalSeries.lean |
| --- | --- |
| **Proposed disposition** | Retain only results not already in Mathlib; state them with the canonical Orthogonal predicate. |
| **Readiness** | Unknown until reuse grep is completed. |
| **Primary review risks** | Long proof-shaped names, repeated raw inner=0 predicate, likely overlap with existing orthogonal-family summability API. |
| **Likely PR slice** | Small independent PR only if genuinely new. |

#### P0  norm_sq_finset_sum_of_pairwise_inner_eq_zero

**Disposition: Reuse audit / rename**

```lean
theorem norm_sq_finset_sum_of_pairwise_inner_eq_zero {ι : Type*} (f : ι → H) (horth : Pairwise fun i j => ⟪f i, f j⟫_𝕜 = 0) (s : Finset ι) : ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2
```

**Proposed target shape**

```lean
theorem norm_sum_sq_of_pairwise_orthogonal ...
```

- Use Pairwise (Orthogonal 𝕜 on f) or the exact canonical Mathlib predicate.

- Search existing Hilbert-space tsum/Pythagorean lemmas before retaining.

- Shorten names after the predicate carries the orthogonality semantics.

**Likely adversarial review:** The reuse rubric explicitly searches long plumbing proofs and near-clones; this whole file needs an exact duplicate audit.

#### P1  norm_sq_sdiff_sum_of_pairwise_inner_eq_zero

**Disposition: Reuse audit / rename**

```lean
theorem norm_sq_sdiff_sum_of_pairwise_inner_eq_zero {ι : Type*} [DecidableEq ι] (f : ι → H) (horth : Pairwise fun i j => ⟪f i, f j⟫_𝕜 = 0) (s₁ s₂ : Finset ι) : ‖(∑ i ∈ s₁, f i) - ∑ i ∈ s₂, f i‖ ^ 2 = (∑ i ∈ s₁ \ s₂, ‖f i‖ ^ 2) + ∑ i ∈ s₂ \ s₁, ‖f i‖ ^ 2
```

**Proposed target shape**

```lean
private theorem norm_sub_sum_sq_of_pairwise_orthogonal ...
```

- Use Pairwise (Orthogonal 𝕜 on f) or the exact canonical Mathlib predicate.

- Search existing Hilbert-space tsum/Pythagorean lemmas before retaining.

- Shorten names after the predicate carries the orthogonality semantics.

**Likely adversarial review:** The reuse rubric explicitly searches long plumbing proofs and near-clones; this whole file needs an exact duplicate audit.

#### P1  summable_iff_norm_sq_summable_of_pairwise_inner_eq_zero

**Disposition: Reuse audit / rename**

```lean
theorem summable_iff_norm_sq_summable_of_pairwise_inner_eq_zero {ι : Type*} [CompleteSpace H] (f : ι → H) (horth : Pairwise fun i j => ⟪f i, f j⟫_𝕜 = 0) : Summable f ↔ Summable fun i => ‖f i‖ ^ 2
```

**Proposed target shape**

```lean
theorem summable_iff_summable_norm_sq_of_pairwise_orthogonal ...
```

- Use Pairwise (Orthogonal 𝕜 on f) or the exact canonical Mathlib predicate.

- Search existing Hilbert-space tsum/Pythagorean lemmas before retaining.

- Shorten names after the predicate carries the orthogonality semantics.

**Likely adversarial review:** The reuse rubric explicitly searches long plumbing proofs and near-clones; this whole file needs an exact duplicate audit.

#### P1  summable_of_pairwise_inner_eq_zero_of_partial_sum_norm_le

**Disposition: Reuse audit / rename**

```lean
theorem summable_of_pairwise_inner_eq_zero_of_partial_sum_norm_le {ι : Type*} [CompleteSpace H] (f : ι → H) (horth : Pairwise fun i j => ⟪f i, f j⟫_𝕜 = 0) {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ s : Finset ι, ‖∑ i ∈ s, f i‖ ≤ C) : Summable f
```

**Proposed target shape**

```lean
theorem summable_of_pairwise_orthogonal_of_norm_sum_le ...
```

- Use Pairwise (Orthogonal 𝕜 on f) or the exact canonical Mathlib predicate.

- Search existing Hilbert-space tsum/Pythagorean lemmas before retaining.

- Shorten names after the predicate carries the orthogonality semantics.

**Likely adversarial review:** The reuse rubric explicitly searches long plumbing proofs and near-clones; this whole file needs an exact duplicate audit.

#### P1  HasSum.norm_sq_eq_tsum_of_pairwise_inner_eq_zero

**Disposition: Reuse audit / rename**

```lean
theorem HasSum.norm_sq_eq_tsum_of_pairwise_inner_eq_zero {ι : Type*} [CompleteSpace H] {f : ι → H} {z : H} (hsum : HasSum f z) (horth : Pairwise fun i j => ⟪f i, f j⟫_𝕜 = 0) : ‖z‖ ^ 2 = ∑' i, ‖f i‖ ^ 2
```

**Proposed target shape**

```lean
theorem HasSum.norm_sq_eq_tsum_norm_sq (horth : Pairwise (Orthogonal 𝕜 on f)) ...
```

- Use Pairwise (Orthogonal 𝕜 on f) or the exact canonical Mathlib predicate.

- Search existing Hilbert-space tsum/Pythagorean lemmas before retaining.

- Shorten names after the predicate carries the orthogonality semantics.

**Likely adversarial review:** The reuse rubric explicitly searches long plumbing proofs and near-clones; this whole file needs an exact duplicate audit.

## 9. C*-algebra and matrix helpers

### 9.1 SelfAdjointGapInverse.lean

| **Current file** | ForTauCeti/Analysis/CStarAlgebra/SelfAdjointGapInverse.lean |
| --- | --- |
| **Proposed disposition** | Replace existential inverse packaging with IsUnit/inverse theorems; verify existing spectral-radius API. |
| **Readiness** | Medium-low. |
| **Primary review risks** | Likely reuse; noncanonical witness; bundled conjunction; spectrum-over-ℝ conventions. |
| **Likely PR slice** | Prerequisite PR only if absent upstream. |

#### P0  IsSelfAdjoint.norm_le_of_spectrum_subset_Icc

**Disposition: Reuse audit**

```lean
theorem IsSelfAdjoint.norm_le_of_spectrum_subset_Icc {a : A} (ha : IsSelfAdjoint a) {r : ℝ} (hr : 0 ≤ r) (h : spectrum ℝ a ⊆ Set.Icc (-r) r) : ‖a‖ ≤ r
```

**Proposed target shape**

```lean
theorem IsSelfAdjoint.norm_le_of_spectrum_subset_Icc
    (ha : IsSelfAdjoint a) (hr : 0 ≤ r)
    (hσ : spectrum ℝ a ⊆ Set.Icc (-r) r) :
    ‖a‖ ≤ r
```

- The name is already conclusion-oriented.

- Search for self-adjoint norm=spectral-radius and spectrum bounds that make this a one-line corollary.

- Keep only if a direct replacement is absent.

**Likely adversarial review:** Reuse can block this theorem if Mathlib already derives it from the CFC spectrum/norm API.

#### P0  IsSelfAdjoint.exists_two_sided_inverse_of_spectrum_gap

**Disposition: Redesign**

```lean
theorem IsSelfAdjoint.exists_two_sided_inverse_of_spectrum_gap {a : A} (ha : IsSelfAdjoint a) {r : ℝ} (hr : 0 < r) (h : ∀ x ∈ spectrum ℝ a, r ≤ |x|) : ∃ j : A, j * a = 1 ∧ a * j = 1 ∧ ‖j‖ ≤ r⁻¹
```

**Proposed target shape**

```lean
theorem IsSelfAdjoint.isUnit_of_abs_spectrum_ge
    (ha : IsSelfAdjoint a) (hr : 0 < r)
    (hσ : ∀ x ∈ spectrum ℝ a, r ≤ |x|) : IsUnit a

theorem IsSelfAdjoint.norm_inv_le_of_abs_spectrum_ge
    ... : ‖a⁻¹‖ ≤ r⁻¹
```

- Use the canonical inverse after proving IsUnit.

- Split invertibility and norm bound so consumers can use either result.

- Consider formulating the hypothesis as spectrum ℝ a ∩ Ioo (-r) r = ∅ or dist 0 spectrum ≥ r, whichever matches existing API.

**Likely adversarial review:** An existential j with both inverse equations and a bound is not a characteristic C*-algebra API and will be requested to change.

### 9.2 Matrix/Spectrum.lean

#### P1  PosSemidef.eigenvalues₀_eq_zero_of_le

**Disposition: Rename**

```lean
PosSemidef.eigenvalues₀_eq_zero_of_le
```

**Proposed target shape**

```lean
theorem Matrix.PosSemidef.eigenvalues₀_eq_zero_of_rank_le
    (hB : B.PosSemidef) (hrank : B.rank ≤ d)
    (hi : d ≤ i) :
    hB.isHermitian.eigenvalues₀ i = 0
```

- Put rank in the name; it is the decisive hypothesis.

- Check whether the natural conclusion is support/cardinality or zero after rank, with this pointwise theorem as a corollary.

- Use implicit i only if dot notation remains readable.

**Likely adversarial review:** The current name “of_le” does not say what is ≤ what and is not discoverable.

## 10. Measure-theory helpers

| **Current file** | Three ForTauCeti MeasureTheory files |
| --- | --- |
| **Proposed disposition** | Generalize and relocate only after exact Mathlib reuse audit. |
| **Readiness** | Unknown. |
| **Primary review risks** | Proof-specific rate lemmas; generic file names; missing canonical measurable-infimum object; possible existing probability complement facts. |
| **Likely PR slice** | Independent small PRs, not bundled with operator theory. |

#### P0  measurableSet_exists_mem_le

**Disposition: Strengthen / reuse**

```lean
theorem measurableSet_exists_mem_le {Y : Type*} [PseudoMetricSpace Y] {Ω : Type*} [MeasurableSpace Ω] {S : Set Y} (hS : IsCompact S) {F : Y → Ω → ℝ} (hFc : ∀ ω, ContinuousOn (fun y => F y ω) S) (hFm : ∀ y ∈ S, Measurable (F y)) (c : ℝ) : MeasurableSet {ω | ∃ y ∈ S, F y ω ≤ c}
```

**Proposed target shape**

```lean
theorem measurable_iInf_compact
    (hS : IsCompact S)
    (hcont : ∀ ω, ContinuousOn (fun y => F y ω) S)
    (hmeas : ∀ y ∈ S, Measurable (F y)) :
    Measurable (fun ω => ⨅ y : S, F y ω)

-- derive:
theorem measurableSet_exists_mem_le ...
```

- Prefer the measurable value function as the reusable theorem; derive the existential sublevel set.

- Check measurable maximum/minimum theorems and Caratheodory integrand API in Mathlib.

- Rename CompactExists.lean to a canonical measurable-minimum topic.

**Likely adversarial review:** The current theorem is a single sublevel-set consequence rather than the characteristic measurable-infimum result.

#### P0  tendstoInMeasure_of_tendsto_measure_rate_lt_edist

**Disposition: Reuse / rename**

```lean
theorem tendstoInMeasure_of_tendsto_measure_rate_lt_edist [EDist E] {f : ι → α → E} {g : α → E} {rate : ι → ℝ≥0∞} (hrate : Tendsto rate l (𝓝 0)) (h : Tendsto (fun i => μ {x | rate i < edist (f i x) (g x)}) l (𝓝 0)) : TendstoInMeasure μ f l g
```

**Proposed target shape**

```lean
theorem tendstoInMeasure_of_measure_edist_gt_tendsto_zero
    (hrate : Tendsto rate l (𝓝 0))
    (hbad : Tendsto (fun i => μ {x | rate i < edist (f i x) (g x)}) l (𝓝 0)) :
    TendstoInMeasure μ f l g
```

- Choose a name that exposes bad-event measure convergence, not “tendsto_measure_rate_lt_edist” word order.

- Use a nonnegative rate type; ENNReal is natural here.

- Check if this is already the definition or a standard epsilon criterion.

**Likely adversarial review:** The long proof-shaped name is likely to be renamed, and direct duplication of TendstoInMeasure criteria would block.

#### P0  tendstoInMeasure_of_tendsto_measure_rate_lt_dist

**Disposition: Fix rate type / derive**

```lean
theorem tendstoInMeasure_of_tendsto_measure_rate_lt_dist [PseudoMetricSpace E] {f : ι → α → E} {g : α → E} {rate : ι → ℝ} (hrate : Tendsto rate l (𝓝 0)) (h : Tendsto (fun i => μ {x | rate i < dist (f i x) (g x)}) l (𝓝 0)) : TendstoInMeasure μ f l g
```

**Proposed target shape**

```lean
theorem tendstoInMeasure_of_measure_dist_gt_tendsto_zero
    {rate : ι → ℝ≥0} ...
```

- Use ℝ≥0 or require eventual nonnegativity; a negative real rate makes the bad event nearly universal.

- Derive from the edist theorem via coercions.

- Keep only if the metric specialization materially improves use.

**Likely adversarial review:** Generality review will challenge unrestricted real-valued rates and duplicated edist/dist proofs.

#### P1  tendstoInMeasure_of_tendsto_measure_dist_le_rate

**Disposition: Polish / derive**

```lean
theorem tendstoInMeasure_of_tendsto_measure_dist_le_rate [PseudoMetricSpace E] [IsProbabilityMeasure μ] {f : ι → α → E} {g : α → E} {rate : ι → ℝ} (hrate : Tendsto rate l (𝓝 0)) (hmeas : ∀ i, NullMeasurableSet {x | dist (f i x) (g x) ≤ rate i} μ) (hprob : Tendsto (fun i => μ {x | dist (f i x) (g x) ≤ rate i}) l (𝓝 1)) : TendstoInMeasure μ f l g
```

**Proposed target shape**

```lean
theorem tendstoInMeasure_of_measure_dist_le_tendsto_one
    [IsProbabilityMeasure μ]
    (hrate : Tendsto rate l (𝓝 0))
    (hgood : Tendsto (fun i => μ {x | dist (f i x) (g x) ≤ rate i}) l (𝓝 1)) :
    TendstoInMeasure μ f l g
```

- Use a nonnegative rate type.

- Try to remove explicit NullMeasurableSet by assuming measurable f/g or deriving measurability from the distance map.

- Derive through the complement/bad-event theorem and a standard probability measure identity.

**Likely adversarial review:** The signature exposes a per-index measurability obligation that may indicate the theorem is stated one level too low.

#### P0  one_sub_measure_compl_le

**Disposition: Reuse audit**

```lean
theorem one_sub_measure_compl_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Set Ω) : 1 - μ sᶜ ≤ μ s
```

**Proposed target shape**

```lean
theorem one_sub_measure_compl_le_measure
    [IsProbabilityMeasure μ] (s : Set Ω) :
    1 - μ sᶜ ≤ μ s
```

- Rename to include the right-hand side.

- Search for measure_compl_le or ENNReal subtraction lemmas first.

- If measurable s gives equality, expose that standard theorem rather than only the weak nonmeasurable inequality.

**Likely adversarial review:** This is likely a one-line consequence of existing probability-measure API and may not merit a new public declaration.

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

The following clusters are not ready for declaration-level cosmetic polishing. Their public object model must converge with Tau Ceti and Spectra first. The TODOs below describe the desired signature direction rather than exact final declarations.

### 12.1 Rectangular symmetric ideal families

> **P0 extensionality defect**
>
> RectangularSymmetricIdealFamily carries Mem and a total gauge on every operator, but the laws constrain gauge only on members. Two structures can agree on every meaningful ideal element and still differ on nonmembers, defeating a natural extensionality theorem. This matches the Tau Ceti API-design rubric’s “free data” failure mode.

```lean
-- Preferred direction: the gauge is a norm on the carrier, not free data off it.
structure SymmetricOperatorIdealFamily (𝕜) where
  carrier (E F) : Submodule 𝕜 (E →L[𝕜] F)
  normedAddCommGroup (E F) : NormedAddCommGroup (carrier E F)
  completeSpace (E F) : CompleteSpace (carrier E F)
  comp_mem ...
  norm_comp_le ...
  adjoint_equiv ...
  -- invariance / Ky Fan dominance as separate stronger mixins
```

- Replace Mem A plus gauge A with a subtype element A : N E F whose norm is the ideal norm.

- Express zero/add/smul/completeness through standard typeclasses rather than structure fields.

- Allow independent source and target universes; the current one-universe family is unnecessarily restrictive.

- Split the minimal normed operator ideal, symmetric/unitarily invariant structure, and Ky Fan dominance into layered classes.

- Provide extensionality on carrier and norm/invariance data.

- Do not include Davis-Kahan-specific “paper norm” normalization in the generic structure.

### 12.2 Closed and self-adjoint unbounded operators

```lean
-- Avoid a parallel bundled ClosedOperator as the foundation.
namespace LinearPMap

def IsClosed (A : E →ₗ.[𝕜] F) : Prop := IsClosed A.graph

def IsDenselyDefined (A : E →ₗ.[𝕜] F) : Prop := Dense (A.domain : Set E)

theorem isClosed_of_isSelfAdjoint ...

def MapsDomainTo (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F)
    (X : F →L[𝕜] E) : Prop := ...

-- Thin bundles only if a roadmap API demonstrably benefits:
structure SelfAdjointOperator where
  toLinearPMap : H →ₗ.[ℂ] H
  selfAdjoint : IsSelfAdjoint toLinearPMap
```

- Rewrite ClosedOperator consumers onto LinearPMap and predicates before upstreaming any theorem.

- Derive density, symmetry, and closedness from self-adjointness rather than store redundant fields.

- Replace SameDomain records with equality of LinearPMap.domain or a simple predicate only when necessary.

- Represent bounded operators through the existing LinearPMap full-domain constructor, not a second closed-operator embedding.

- Make graph norm and bounded-extension constructions operate on the domain subtype of a LinearPMap.

- Coordinate naming with Tau Ceti semigroup generator files, which already use LinearPMap.

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

| **Cluster** | **Current state** | **Signature risk** | **Upstream action** | **Priority** |
| --- | --- | --- | --- | --- |
| operatorAbs | Special case duplicate of rectangular modulus | Delete definition; retain compatibility theorem/notation temporarily | DavisKahan.Interop.TauCeti | P0 |
| ClosedOperator | Parallel bundle over LinearPMap | Demote to adapter, then delete from generic production | DavisKahan.Interop.TauCeti | P0 |
| Spectra SelfAdjointOperator | Potential donor wrapper | Port useful lemmas; choose canonical Tau Ceti representation | Short-lived conversion functions | P1 |
| specSubspace | Misnamed coordinate span | Rename/move; compatibility alias only downstream if needed | Deprecated local alias | P0 |
| finiteMean / appendFin | Likely generic duplicates | Replace with Finset/Fintype API | No upstream adapter | P0 |
| RectangularSymmetricIdealFamily | Free-data structure | Replace with normed carrier/family | Adapter from old Mem/gauge for DK proofs | P0 |
| GenuinePairwiseSpectrumGap | Paper/bridge terminology | Replace with canonical separation predicate | Paper wrapper | P1 |

- Adapters must be visibly downstream and carry a deletion condition.

- No adapter should be submitted to Tau Ceti merely to preserve DKPS source compatibility.

- After each canonical API lands, repoint consumers, remove duplicate declarations, and run a grep gate for old fully qualified names.

- Avoid long-lived aliases before upstream review; they obscure which API reviewers are evaluating.

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
| approximationNumber_def | approximationNumber_eq_iInf | Sketch; verify adjacent Mathlib naming |
| approximationNumber_le | approximationNumber_le_nnnorm_sub | Sketch; verify adjacent Mathlib naming |
| approximationNumber_eq | approximationNumber_eq_nnnorm_sub_of_isLeast | Sketch; verify adjacent Mathlib naming |
| lt_approximationNumber_add_pos | exists_rank_le_nnnorm_sub_lt_approximationNumber_add | Sketch; verify adjacent Mathlib naming |
| approximationNumber_add_le | approximationNumber_add_le_add_nnnorm | Sketch; verify adjacent Mathlib naming |
| approximationNumber_add_le_add | approximationNumber_add_le | Sketch; verify adjacent Mathlib naming |
| singularValues_le_norm_sub_of_rank_le | singularValue_le_norm_sub_of_rank_le | Sketch; verify adjacent Mathlib naming |
| approximationNumber_eq_singularValues | approximationNumber_eq_singularValue | Sketch; verify adjacent Mathlib naming |
| lowerBound_le_approximationNumber_of_finrank | le_approximationNumber_of_finrank_lt | Sketch; verify adjacent Mathlib naming |
| specSubspace | OrthonormalBasis.spanIndices | Sketch; verify adjacent Mathlib naming |
| forall_unit_vector_eigenvalue_le_re_inner | exists_submodule_forall_unit_eigenvalue_le_re_inner | Sketch; verify adjacent Mathlib naming |
| abs_eigenvalues_sub_le_opNorm | abs_eigenvalue_sub_eigenvalue_le_norm | Sketch; verify adjacent Mathlib naming |
| eigenvalues_le_eigenvalues_of_re_inner_le | eigenvalue_mono | Sketch; verify adjacent Mathlib naming |
| rectangularOperatorModulus | ContinuousLinearMap.modulus | Sketch; verify adjacent Mathlib naming |
| operatorAbs | delete; square specialization of modulus | Sketch; verify adjacent Mathlib naming |
| finiteMean | Finset.mean / existing average | Sketch; verify adjacent Mathlib naming |
| centeredScatter | scatterOperator | Sketch; verify adjacent Mathlib naming |
| appendFin | delete; existing Fin combinator | Sketch; verify adjacent Mathlib naming |
| PosSemidef.eigenvalues₀_eq_zero_of_le | eigenvalues₀_eq_zero_of_rank_le | Sketch; verify adjacent Mathlib naming |
| exists_two_sided_inverse_of_spectrum_gap | isUnit_of_abs_spectrum_ge + norm_inv_le... | Sketch; verify adjacent Mathlib naming |

## Appendix B. Review questions to answer in roadmaps

1. Which approximation-number index convention is canonical for Tau Ceti, and why?

1. Should approximation numbers be ℝ-valued or ℝ≥0-valued?

1. Should the definition extend ContinuousLinearMap or live under TauCeti?

1. What is the canonical name for the source modulus of a rectangular operator?

1. Which existing Mathlib CFC square-root declarations make modulus lemmas redundant?

1. What exact Courant-Fischer equality is the roadmap product, rather than merely a support lemma?

1. Does Tau Ceti want a bundled SelfAdjointOperator, or properties on LinearPMap?

1. What is the minimal PVM/Borel-calculus slice to port from Spectra?

1. What single Hilbert-Schmidt predicate and norm will tensor, column, and singular-value characterizations share?

1. How should a symmetric operator ideal be represented so equality/extensionality ignores nonmembers?

1. Which generic Haagerup-Zsido prerequisites belong in Mathlib-like files, and which should remain private?

1. Which downstream paper aliases are explicitly excluded from Tau Ceti?

## Source basis

Repository audit: aiq-dkps-formalization archive 543b46f42573, including ForTauCeti, ForMathlib, DavisKahan, external/TauCeti, and dev/tauceti planning files.

Review criteria: TauCetiProject/TauCeti AGENTS.md and TauCetiProject/TauCetiReview rubrics at review commit b9539a39556d34b3e3bf6199d0da7b4e7d5d4c27 (correctness, reuse, scope, attribution, API design, generality, placement, naming, documentation, proof quality).

Internal polishing guidance: dev/mathlib-proof-polishing.md and dev/mathlib-quality-adapter.md.
