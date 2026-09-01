iYou are taking over `aiq-dkps-formalization` at the final stage of the Davis–Kahan 1970 formalization and Palomar extraction.

Your job is to **finish this task completely**.

Do not stop after identifying the remaining obstruction. Do not stop after proving one intermediate transport lemma. Do not stop after making the census green. Do not stop after producing a Challenge containing `sorry`s if the production theorem is still incomplete. Drive the repository to the end-state described below, subject only to a genuinely unavoidable external dependency or policy obstruction that you can demonstrate concretely.

Inspect the current repository before changing anything. Current source beats this prompt, prior reports, theorem names, comments, inventories, and commit messages.

Read at minimum;

* `AGENTS.md`
* `GOAL.md`
* the Davis–Kahan 1970 source/result inventory and its contract
* the coherent-evidence/source-clause checker
* its regression tests
* generated semantic/source audit documents
* `DavisKahan/Sources/DavisKahan1970/SectionTwo.lean`
* all four Section 2 theorem developments
* the directed and ambient `sin 2Θ` files
* the unbounded double-angle/reflection developments
* the generic `sin Θ` paper surface
* the newly added unbounded directed `tan Θ` endpoints
* the real transport/complexification developments
* Challenge/Palomar directories
* the standalone Palomar/Davis–Kahan submodule if present
* current Palomar policy/template
* the exact pinned Tau Ceti revision and its actual contents

Use the Davis–Kahan paper itself when deciding source semantics. The maintained source inventory is evidence and bookkeeping: it is not a substitute for checking the paper.

# End-state

The task is complete only when all of the following are true.

## Mathematical completeness

1. The missing full-scope **ambient `sin 2Θ` theorem** exists over `ℂ`.
2. The corresponding theorem exists over `ℝ`.
3. They use the actual ambient double-angle object, not the directed/block surrogate.
4. They hold for arbitrary `PaperUnitaryInvariantNorm`.
5. They cover the actual unbounded/self-adjoint source scope.
6. They preserve the full source separation alternatives, including half-infinite configurations where Davis–Kahan permit them.
7. They conclude ideal membership as required by the production paper-norm interface.
8. The factor is exactly `2`.
9. No implementation-only hypothesis has been inserted into the source theorem.
10. No operator-norm/Ky-Fan/finite-dimensional specialization is substituted for the paper theorem.

## Certificate completeness

11. The coherent source-clause inventory is **81/81 established**, assuming 81 remains the correct count after inspection.
12. Every counted Davis–Kahan result has been subjected to the hostile statement-correspondence audit.
13. The result denominator remains the actual 29 paper results unless inspection of the paper discovers a genuine denominator error.
14. Only after that audit is complete may the repository again advertise **29/29 paper-faithful**.
15. The checker must continue rejecting the old cross-declaration “Frankenstein” evidence composition.
16. Scalar coverage, clause coherence, operator scope, norm scope, gap scope, and correspondence evidence must remain compiler-auditable.

## Section 2 API completeness

17. All four Section 2 headline results have a source-facing representation that exposes the complete paper result.
18. Directed and ambient clauses are named explicitly where the paper contains both.
19. `sin 2Θ` gains the missing full-scope ambient aliases over both fixed fields.
20. The short headline names do not point to only one clause while documentation claims they represent the full theorem.
21. The final public source boundary exposes clean generic `[RCLike 𝕜]` forms for all four headline results, without implementation capability classes in the public theorem whenever those classes can be discharged internally by real/complex dispatch.
22. Existing fixed-field real and complex endpoints remain available as implementation/certification artifacts.

## Palomar completeness

23. There is a real compiling candidate `Challenge.lean`, under current Palomar limits, containing the actual four full unbounded Section 2 results rather than weakened specializations.
24. It imports only dependencies permitted on the Challenge side.
25. No DKPS-private definition appears transitively in the Challenge statement environment.
26. No local/unmerged Tau Ceti addition is accidentally treated as upstream.
27. The four headline Challenge declarations are generic over `[RCLike 𝕜]` if mathematically possible without additional assumptions.
28. The Challenge contains every directed/ambient clause belonging to each of the four source results.
29. A comparator/correspondence layer proves that the Challenge vocabulary means exactly what the production DKPS vocabulary means.
30. A Solution/proof route exists under Palomar's actual dependency rules and proves the four Challenge results, not merely a weaker production cousin.
31. Exact Challenge line and byte counts are measured.
32. The final report gives a concrete Palomar readiness verdict.

Do not call the task finished before reaching that state.

---

# Current verified state to preserve

The latest implementing-agent report established several important facts. Verify them in the repository, then treat them as constraints unless current source contradicts them.

## Coherent evidence checker

The former result-wide flat union has already been replaced.

The current design uses concepts named approximately;

```text
result_wide_scope_atoms
source_clauses
```

with one primary witness per printed clause per scalar field, and the old hand-authored `covers_source_atoms` union is gone or derived.

Current reported status;

```text
81 source clauses
79 established
2 open
```

The two open obligations are the real and complex ambient `sin 2Θ` clauses.

The checker now requires a primary witness to satisfy the type requirements associated with that clause's conclusion and the result-wide scope.

The old invalid construction;

```text
unbounded directed theorem
+
bounded ambient theorem
-------------------------
"unbounded ambient theorem"
```

must remain rejected.

There are seven reported checker regression tests and they are green.

Do not regress this architecture back to result-wide atom union.

## Half-infinite gap handling

The current checker deliberately does not identify half-infinite scope by requiring a literal `FormBoundedSylvesterGap` token.

That is correct in principle because the different theorem families spell the same source scope differently;

* some use `FormBoundedSylvesterGap`:
* the tangent family uses an ordered formulation:
* `tan 2Θ` may expose bare form bounds.

The current mechanism instead requires an explicit per-clause justification for the half-infinite-gap source scope.

Preserve this flexibility, but audit each justification. It must explain a real mathematical/type-level correspondence, not become a free-form escape hatch.

If practical, strengthen these justifications with compiled predicates or correspondence lemmas. Do not force unrelated theorem families into one implementation spelling merely to simplify Python.

## `tan Θ`

The earlier certificate was wrong because the registered witnesses were not full-scope directed witnesses.

That mathematical issue has reportedly been repaired.

The relevant new production endpoints are approximately;

```text
theorem6_3_unbounded_infiniteTrial_ideal
tanTheta_directed_unboundedTrial_paperUINorm_complex
tanTheta_directed_unboundedTrial_paperUINorm_real
```

The key distinction was that the old existential ideal theorem selected a potentially different representative for each Ky Fan index, so it could not simply be promoted to one arbitrary paper UI norm. A parameterized spectral-gap form was required.

Verify the final theorem types and preserve this repair.

Do not allow future audits to fall back to;

```text
theorem6_3_perturbation_infiniteTrial
```

if its ambient operator is bounded, or to a finite-dimensional rectangular-seminorm facade.

The directed source theorem needs the directed `tan Θ₀`, the source residual `R`, unbounded source operators, the correct ordered/half-infinite gap scope, arbitrary UI norm, and both scalar fields.

## `DK-4.2-prop`

The new scalar-coverage check reportedly found that the real counterpart had been treated only as supporting evidence even though the source result covers both fields.

That counterpart has now been promoted.

Preserve that correction and inspect the other 29 rows for the same class of mistake.

Supporting evidence over the missing field is not enough when the paper result itself has that scalar scope.

## Section 2 aliases

The current tree reportedly has explicit `_directed_` and `_ambient_` fixed-field aliases for the three headline results that have both directed and ambient clauses.

`sin 2Θ` intentionally lacks a full-scope ambient alias because no honest theorem currently exists to bind it to.

That is the right temporary state.

Once the missing theorem is proved, fill this hole with the new full-scope theorem. Do not bind the alias to the old bounded ambient result.

---

# Primary mathematical task; prove ambient unbounded `sin 2Θ`

This is the remaining known correctness blocker.

The source ambient clause is genuinely distinct from the directed clause.

The desired fixed-field theorem has the mathematical shape;

```lean
N.Mem (paperSinTwoAngleOperator... U V) ∧
  δ * N.gauge (paperSinTwoAngleOperator... U V)
    ≤ 2 * N.gauge H
```

with the exact production source vocabulary appropriate to each field.

The theorem must have;

* unbounded self-adjoint source operator:
* bounded self-adjoint perturbation `H`:
* arbitrary Hilbert dimension:
* arbitrary paper UI norm:
* the full source spectral separation:
* half-infinite alternatives:
* the actual **ambient** `sin 2Θ` object:
* ideal membership:
* exact factor `2`.

Do not discharge this with the one-sided `sinTwoThetaIdealBlock`.

Do not discharge this with the directed `sinTwoAngleOperatorC`.

Do not use operator norm equality to infer arbitrary UI norm equality when multiplicities differ.

The repository already records that the one-sided/directed representation carries principal-angle singular data with different multiplicity from the ambient operator. Respect that distinction.

---

# Expected proof route

The latest report has already identified a promising route. Treat it as the starting point and test it against actual types.

There is an existing correspondence around;

```text
paperSinTwoAngleOperatorC_eq_modulus_starProjection_sub
```

which identifies the ambient `sin 2Θ` object with the modulus associated to a projector-difference/reflection picture.

There is also now an unbounded symmetric sine-theorem layer involving approximately;

```text
PaperCommonDomainSymmetricSinThetaProblem
```

Inspect the exact declaration names and types. Do not assume from the name that this symbol itself is the theorem you need.

The intended mathematical reduction is;

```text
ambient sin 2Θ for U,V
        |
        | reflection of V
        v
ambient sin Θ between U and reflected U
        |
        | unbounded symmetric sin Θ theorem
        v
UI-norm bound by displacement of reflected operator
        |
        | reflection algebra
        v
≤ 2 * UI-norm of H
```

The previous agent identified three missing transport ingredients.

Implement them cleanly rather than routing around them with source-weaker assumptions.

## 1. Transport of reducing subspaces through the reflection unitary

You need the exact theorem that transports the relevant `ReducesSubspace` fact under the reflection/unitary map.

Derive its statement from the definitions actually used by the symmetric unbounded sine theorem.

The result should be reusable and live at the mathematically appropriate layer, not as a theorem hard-coded to the final `sin 2Θ` proof if it is genuinely general.

It should establish that the reflected/mapped subspace reduces the unitary-conjugated operator under the assumptions already available.

Do not add a reducing assumption on the reflected side if it follows from the original reducing hypothesis.

## 2. Identify reducing restriction after reflection with unitary conjugation

Prove the required relationship involving the actual forms of;

```text
reducingRestriction B (U.map R_V)
```

and the appropriate;

```text
unitaryConjugate ...
```

of the original restricted operator.

The exact orientation of the equivalence/conjugation should follow the repository definitions.

Prefer literal equality when the objects are definitionally/extentionally equal.

If literal equality is representation-inappropriate, prove the strongest exact equivalence needed by the next theorem and document what is being transported.

Do not settle for a norm inequality if the proof needs spectral equivalence.

## 3. Invariance of `FormBoundedSylvesterGap` under unitary conjugation

Prove an actual reusable transport theorem.

A unitary conjugation should preserve the spectral/form geometry relevant to the source separation condition.

The goal is to carry the full gap object through the reflection argument without replacing it with a finite interval specialization.

Make sure the theorem handles every constructor/case of `FormBoundedSylvesterGap`, including the half-infinite configurations.

Do not prove only the bounded-interval constructor and leave the others inaccessible.

If the correct abstraction is a more general equivalence/invariance theorem from which the gap transport follows, implement that instead.

## Use the transport lemmas to instantiate the symmetric sine theorem

Once those three pieces exist;

1. construct the reflected unbounded problem:
2. prove all domain/self-adjointness/common-domain/reduction facts required by the symmetric `sin Θ` result:
3. transport the source gap to the reflected pair:
4. invoke the arbitrary-paper-UI-norm symmetric theorem:
5. identify its angle object with the actual ambient `paperSinTwoAngleOperatorC`:
6. obtain ideal membership for the actual ambient object:
7. derive the exact constant `2` from the reflection displacement:
8. conclude the source theorem.

At every step prefer theorem-level correspondences over comments claiming two implementation objects represent the same source quantity.

---

# Complex theorem first

Complete the complex theorem first if that remains the natural proof base.

Add a source-facing theorem whose name makes its scope clear, approximately;

```lean
sinTwoTheta_ambient_unbounded_addBounded_paperUINorm_complex
```

The exact name can differ if repository conventions suggest a better one.

Inspect the final printed type.

The type itself should make clear that this is;

* ambient:
* unbounded:
* additive bounded perturbation:
* arbitrary paper UI norm:
* full gap scope.

Then add or update the fixed-field source alias in `SectionTwo.lean`.

Do not certify the clause through an internal theorem with a misleading name when a thin source facade can expose the exact source statement.

---

# Real theorem

After the complex theorem works, provide the real endpoint at exactly the same source strength.

Prefer the repository's established real/complexification architecture rather than duplicating a very large analytic proof.

But do not assume complexification automatically preserves everything required by the arbitrary paper UI norm.

Explicitly verify;

* the real ambient `sin 2Θ` source object corresponds to the complexified object:
* multiplicities are correct:
* paper UI norm membership transports correctly:
* gauge values correspond correctly:
* the source spectral-gap condition transports:
* unbounded domains/self-adjointness transport:
* the factor `2` is unchanged.

If a direct real reflection proof is shorter and cleaner using existing real infrastructure, use it.

Add a theorem approximately;

```lean
sinTwoTheta_ambient_unbounded_addBounded_paperUINorm_real
```

and the corresponding `SectionTwo` alias.

The real theorem is a canonical source witness, not merely supporting documentation.

---

# Close the coherent source-clause inventory

Once both fixed-field ambient theorems exist;

1. register the complex ambient `sin 2Θ` clause against the complex theorem:
2. register the real ambient clause against the real theorem:
3. remove any temporary `open` status:
4. ensure the clause scope is derived from the theorem type and explicit justified correspondences:
5. run the checker:
6. confirm that all 81 clauses are established if 81 is still the correct source-clause total.

Do not make the checker green by weakening a type requirement or moving the source fact into an unconstrained prose field.

The checker should have rejected the repository before these theorems existed and accept it afterward because the mathematical evidence changed.

That before/after distinction is essential.

---

# Audit the checker itself after the theorem repair

The new checker is much stronger than the old one, but it is new code and needs a hostile review too.

Inspect the schema and tests for loopholes.

For every `source_clause`, ask;

* Does it name exactly one printed source clause?
* Is its scalar field explicit when the paper covers both real and complex?
* Is the primary theorem actually inspected rather than trusted by declaration name?
* Do conclusion requirements attach to that primary theorem?
* Do result-wide scope requirements attach coherently to the same theorem/evidence chain?
* Are correspondence lemmas explicit?
* Can an unrelated theorem donate a missing scope property?
* Can prose justification override a compiler-visible contradiction?
* Can supporting evidence accidentally satisfy a canonical obligation?
* Can an `open` clause be counted as established?
* Can generated counts disagree with schema state?

Keep the existing negative regression for the old `sin 2Θ` composition.

Also add regression coverage for any loophole you discover during this final audit.

The checker should support legitimate cases such as;

* one theorem stronger than the printed theorem because it drops a source assumption:
* fixed real and complex siblings:
* separately quantified directed and ambient clauses:
* explicit theorem + correspondence chain:
* alternative source hypotheses:
* different but equivalent gap encodings.

Do not reintroduce informal result-wide set union to handle these cases.

---

# Audit all 29 paper results under the new semantics

Do not restore `29/29` immediately after the last two clauses turn green.

The source-clause checker was introduced because the previous completion certificate was able to assert a conjunction that no theorem established. Now use the stronger machinery to re-review the whole paper.

For each of the 29 counted results, perform the hostile statement-correspondence check.

For every printed result record;

1. exact source location/result:
2. exact printed/source mathematical statement:
3. every separately quantified clause:
4. source scalar scope:
5. bounded/unbounded operator scope:
6. domain assumptions:
7. dimension scope:
8. norm scope:
9. spectral-gap/separation alternatives:
10. residual versus ambient perturbation:
11. directed versus ambient angle:
12. constants:
13. multiplicity-sensitive representation issues:
14. pole/smallness assumptions where applicable:
15. canonical Lean witness for each field/clause:
16. correspondence lemmas used:
17. every apparent difference between source and Lean:
18. whether Lean is equivalent, stronger, or genuinely different:
19. final disposition; `PASS` or `OPEN`.

Use the paper, not only the result inventory.

`DK-4.2-prop` already demonstrated that scalar coverage could previously be hidden in supporting evidence. Search specifically for other rows with that pattern.

Search specifically for;

* a bounded theorem donating a conclusion to an unbounded row:
* a finite-dimensional theorem donating a conclusion to an infinite-dimensional row:
* an operator-norm theorem donating a conclusion to an arbitrary-UI row:
* one scalar field being canonical while the other is merely supporting:
* directed and ambient quantities being conflated:
* source gap alternatives being split across incompatible witnesses:
* source-required hypotheses dropped accidentally because an implementation theorem proves a different statement:
* implementation-only assumptions added to a source theorem:
* constants changing through representation transport.

Do not assume a green Python checker makes this manual/semantic pass redundant.

If you find another real mathematical gap, fix it before completion.

If the Lean theorem is stronger, record exactly why stronger implies the source statement.

If a representation differs, supply a compiled correspondence theorem where feasible.

Only after every one of the 29 rows is `PASS` may generated material state `29/29`.

---

# Preserve the denominator semantics

Do not undo the earlier correction concerning result-adjacent extensions.

The denominator consists of substantive results Davis and Kahan introduce and prove as results.

It is not;

* every equation:
* every proof step:
* every source atom:
* every mathematical sentence:
* every later remark:
* every immediate consequence:
* every sentence saying a proof extends analogously.

The four later extension passages that were reclassified as;

```text
result_adjacent_extension
```

should remain outside the denominator unless re-reading the paper establishes that Davis and Kahan actually present and prove another counted result there.

Proofs of those extensions may remain in Lean as useful supporting mathematics.

Do not delete correct stronger results merely because they are not denominator obligations.

---

# Clean up the Section 2 production surface

The production source boundary should become readable as Davis–Kahan Section 2, rather than exposing whichever internal theorem happened to be convenient.

Keep a clear distinction between;

```text
source mathematical vocabulary
public source theorem
proof implementation
```

Proof implementation may contain;

* CFC/PVM machinery:
* complexification:
* operator ideals:
* approximation-number families:
* reflection/unitary transport:
* capability classes:
* fixed-field specialization records.

That complexity does not need to leak into the public paper theorem.

## Fixed-field clause aliases

For the three multi-clause headline results, provide explicit fixed-field aliases for each clause.

Conceptually;

```text
tanTheta_directed_complex
tanTheta_ambient_complex
tanTheta_directed_real
tanTheta_ambient_real

sinTwoTheta_directed_complex
sinTwoTheta_ambient_complex
sinTwoTheta_directed_real
sinTwoTheta_ambient_real

tanTwoTheta_directed_complex
tanTwoTheta_ambient_complex
tanTwoTheta_directed_real
tanTwoTheta_ambient_real
```

Use repository naming conventions rather than these exact strings if needed.

After this task there must be no bounded theorem bound to an alias whose name/documentation implies the full unbounded source result.

## Headline theorem representation

Three of the four Section 2 results contain directed and ambient clauses.

Do not solve that presentation issue by forcing both clauses into one common telescope containing hypotheses irrelevant to one clause.

That changes the source statement.

Instead design a compact source-facing representation that preserves the natural quantification of the clauses.

Possible designs include;

* a source proposition whose fields/clauses quantify their own data:
* a small source-result structure with directed and ambient proof fields:
* namespaced clause theorems plus a headline certificate object:
* another equally explicit representation.

Choose based on the actual paper syntax and theorem telescopes.

The reviewer should be able to look at the source-facing definitions immediately above the theorem and recognize Davis–Kahan's theorem.

---

# Finish the generic `[RCLike 𝕜]` source boundary

Fixed `ℝ` and `ℂ` theorems establish the paper's scalar cases, but the desired final public API is cleaner.

The target is four source-facing headline declarations conceptually named;

```lean
SectionTwo.sinTheta
SectionTwo.tanTheta
SectionTwo.sinTwoTheta
SectionTwo.tanTwoTheta
```

over;

```lean
{𝕜 ; Type*} [RCLike 𝕜]
```

These names should represent the complete source results, not a random single clause.

Keep the fixed-field endpoints behind them.

## Do not fake genericity

Do not merely introduce a generic theorem with extra typeclasses that happen to have instances only for `ℝ` and `ℂ`.

The public source theorem should not expose implementation capability classes if those capabilities can be discharged by dispatching to the real or complex proof.

Inspect current Mathlib's actual `RCLike` classification/equivalence APIs.

Do not invent API names based on this prompt.

The intended implementation shape is;

```text
generic source data over 𝕜
        |
        | classify/transport RCLike field
        |
   +----+----+
   |         |
   v         v
   ℝ         ℂ
   |         |
fixed     fixed
theorem   theorem
   |         |
   +----+----+
        |
transport result back
```

All mathematical objects used in the source theorem must transport coherently;

* Hilbert spaces:
* `LinearPMap` operators:
* self-adjointness:
* domains:
* spectral/reducing subspaces:
* source gap predicates:
* residuals:
* angle objects:
* paper UI norm data:
* ideal membership and gauge values.

Do not make the final theorem weaker to make transport easier.

## Existing `sin Θ`

The existing generic `sin Θ` theorem is the reference implementation, but review its final signature too.

If it still exposes implementation-only capability classes, either;

* hide them behind a cleaner source facade using real/complex dispatch: or
* establish that they are genuinely mathematical hypotheses already present in Davis–Kahan.

Do not simply preserve them because the old theorem compiled.

The end-state is a source theorem a hostile reviewer can compare directly to the paper.

---

# Palomar Challenge; now finish it

Once production mathematics is complete, turn the Section 2 source boundary into a real Palomar candidate.

Do not leave this as a feasibility note.

Inspect the **current** Palomar policy and template first.

Verify;

* hard Challenge line limit:
* hard byte limit:
* warning thresholds:
* allowed Challenge imports:
* treatment of `sorry` in Challenge:
* Solution dependency rules:
* exact Tau Ceti allowlist/pinned-history requirements:
* whether Challenge-local definitions are permitted:
* any restrictions added since earlier work.

Do not rely on remembered policy numbers without checking the current files/site used by the project.

The previous review found a hard ceiling around 1000 lines / 100 KiB, with lower warning thresholds, but current policy is authoritative.

## Challenge dependency boundary

`Challenge.lean` may use only the dependencies Palomar permits on the statement side.

In particular, distinguish;

1. Lean/Mathlib:
2. released/upstream Tau Ceti at an allowlisted revision:
3. local Tau Ceti additions intended for future upstreaming:
4. DKPS-local infrastructure.

Only categories actually allowed by current policy belong in Challenge.

The Challenge must not import DKPS itself just to obtain convenient definitions.

Audit the transitive import graph, not only the explicit import lines.

## Source vocabulary, not production vocabulary

Do not copy production theorem types mechanically.

Production contains abstractions that were created to make proofs work.

Examples include;

* `PaperUnitaryInvariantNorm`:
* proof-oriented ideal-family infrastructure:
* specialized spectral restriction records:
* CFC/PVM representations:
* capability classes:
* complexification support:
* DKPS-local full-gap records.

Ask instead;

> What is the smallest explicit mathematical vocabulary needed to state Davis–Kahan's four Section 2 results exactly?

Define compact Challenge-local source objects where policy permits and where upstream Tau Ceti lacks the right abstraction.

Every compact definition must later receive an exact comparator against production.

Do not replace arbitrary UI norms with operator norm.

Do not replace unbounded operators with bounded operators.

Do not replace real+complex with complex-only.

Do not replace half-infinite gaps with finite intervals.

Do not replace ambient angle operators with directed blocks.

## Four final headline declarations

The desired reader-facing Challenge surface should contain exactly four headline results corresponding to the four Section 2 theorems;

```lean
theorem sinTheta ...
theorem tanTheta ...
theorem sinTwoTheta ...
theorem tanTwoTheta ...
```

Prefer;

```lean
{𝕜 ; Type*} [RCLike 𝕜]
```

for scalar scope.

For the three source results with multiple clauses, the theorem conclusion may use a compact source result proposition/structure so that one headline declaration still represents the whole paper result without forcing unrelated hypotheses into one telescope.

A hostile reviewer should be able to compare each Challenge theorem to Davis–Kahan and see;

* same scalar scope:
* same operator scope:
* same separation alternatives:
* same norm quantification:
* same directed/ambient clauses:
* same residual/perturbation quantities:
* same constants:
* same standing assumptions.

---

# Build the production ↔ Challenge comparator

Do not accept a Challenge because it “looks right.”

Inside the full DKPS environment, build correspondence proofs between every Challenge source object and its production counterpart.

For each of the four headline results;

1. identify the production fixed-field theorem(s):
2. identify every Challenge-local source definition:
3. prove the Challenge definition corresponds to production over `ℂ`:
4. prove correspondence over `ℝ`:
5. prove any generic `[RCLike]` representation is transported correctly:
6. derive the Challenge theorem from the production theorem:
7. where practical, mechanically compare normalized theorem propositions:
8. ensure no additional premise appears during correspondence.

Important correspondence targets include;

* self-adjoint unbounded operator representation:
* source spectral separation:
* half-infinite alternatives:
* reducing spectral subspaces:
* residual definitions:
* directed angle objects:
* ambient angle objects:
* UI norm quantification:
* ideal membership:
* multiplicity-sensitive singular data.

Literal equality is ideal when true.

When literal equality is representation-dependent, use the strongest exact invariant actually needed by the theorem, such as equality of the relevant UI-norm quantity or singular-value sequence.

Do not substitute a one-sided inequality and call it correspondence.

---

# Build/finish the Palomar Solution

After Challenge and comparator are sound, make the Palomar Solution actually prove the Challenge theorems under current policy.

Use whatever proof dependencies Palomar currently allows on the Solution side.

The Solution may be implementation-heavy.

That is acceptable.

The Challenge is the source-facing artifact: the Solution may contain the fixed-field dispatch, complexification, reflection machinery, operator ideals, and correspondence layer.

But the final build must close the actual four Challenge declarations.

If Challenge is intentionally allowed to contain `sorry` placeholders by Palomar convention, the separate Solution still needs to prove the corresponding theorem statements.

Do not call a statement-only spike the finished submission.

---

# Keep the Challenge comfortably within budget

Measure;

```text
line count
byte count
number of imports
number of local definitions
number of headline theorems
```

Also give a rough line breakdown by source concept;

* scalar/Hilbert setup:
* unbounded operator/source spectral vocabulary:
* gap/separation vocabulary:
* UI norm vocabulary:
* angle vocabulary:
* residual vocabulary:
* result containers for multi-clause theorems:
* four declarations.

Optimize duplicated statement vocabulary.

Do not optimize by weakening the theorem.

If the Challenge exceeds the hard limit, identify the exact source-vocabulary component consuming the budget and determine whether;

* it can be stated more compactly:
* an existing upstream Tau Ceti definition can replace it:
* a small specific upstream Tau Ceti addition is needed.

Only after attempting the real artifact may you conclude that a dependency change is necessary.

---

# Upstream Tau Ceti audit

The production repository contains concepts that upstream Tau Ceti may not.

Build an explicit table/list for every production concept needed by the four Section 2 statements;

```text
concept
production symbol
exists upstream? yes/no
Challenge needs it? yes/no
Solution only? yes/no
compact Challenge replacement?
future upstream candidate?
```

Pay special attention to;

* `LinearPMap`:
* spectrum/resolvent machinery:
* self-adjointness:
* reducing restrictions:
* unitarily invariant norm vocabulary:
* `FormBoundedSylvesterGap`:
* reflection/unitary conjugation:
* source angle objects.

Use actual upstream source at the pinned revision.

Do not assume a definition is upstream because it lives under a Tau Ceti-looking namespace in the DKPS checkout.

---

# Documentation cleanup

Once the mathematical state is final, make all normative documentation agree with it.

Clean up;

* stale statements that later result-adjacent extensions “have to be covered” by the denominator:
* stale source-atom counts:
* stale five-category wording if six categories now exist:
* old statements that one-clause aliases represent “both printed conclusions”:
* obsolete notes saying the full-gap `sin 2Θ` theorem is missing:
* old descriptions of `tan Θ` as lacking full-scope directed paper-norm endpoints:
* any generated audit that still describes 79/81 after the repair:
* any completion banner restored before hostile review is complete.

Historical logs may describe old states when clearly labeled as history.

Do not rewrite history simply to make old entries sound current.

Regenerate machine-generated artifacts from their canonical source rather than manually editing generated output.

---

# Validation

Run the repository's actual required gates.

At minimum;

```text
lake build
lake build Challenge
lake build DavisKahan.Audits.All
```

plus;

* source/result inventory checker:
* semantic correspondence checker:
* source-clause checker:
* checker regression tests:
* drift/generated-file checks:
* any Palomar validation scripts:
* any standalone Challenge/Solution build in the Palomar dependency environment.

The previous state reportedly had;

```text
9709 green
Challenge green
Audits.All green
four pre-existing gate failures unchanged
```

Do not introduce new unrelated failures.

If those four pre-existing failures remain, identify them exactly and show that their counts/diagnostics are unchanged.

For every new production theorem, check for accidental trust holes.

No new;

```text
sorry
admit
axiom
```

in production proof files.

Use `#print axioms` or the repository's equivalent trust audit on the final headline witnesses where practical.

Challenge-side `sorry` is only acceptable if current Palomar policy explicitly uses that convention: it does not excuse an incomplete Solution.

---

# Final hostile review of the four Section 2 theorems

Before declaring Palomar ready, write a concise but exact comparator for each headline theorem.

For each of;

```text
sin Θ
tan Θ
sin 2Θ
tan 2Θ
```

show;

## Source

The mathematical Davis–Kahan statement, including all clauses.

## Production

The exact fixed-field real and complex canonical theorem(s).

## Public generic surface

The final `[RCLike 𝕜]` theorem/result object.

## Palomar

The exact Challenge declaration.

## Correspondence

Explain every nontrivial translation;

* source interval/separation language:
* `LinearPMap` representation:
* residual:
* angle operator:
* directed versus ambient form:
* multiplicity:
* UI norm:
* real/complex dispatch:
* factor:
* extra or dropped hypotheses.

The disposition must be one of;

```text
EXACT
LEAN STRICTLY STRONGER, WITH EXPLICIT REASON
OPEN
```

Anything `OPEN` means the task is not complete.

---

# What not to do

Do not;

* restore 29/29 because a count reaches zero open clauses without reviewing the 29 results:
* weaken `sin 2Θ` to operator norm:
* use the directed block as the ambient arbitrary-UI object:
* bind the full-source alias to a bounded theorem:
* lose the real case:
* lose half-infinite gap configurations:
* force every theorem family to spell the gap using the same implementation record:
* add implementation capability classes to the source theorem merely because an internal proof uses them:
* add a `tan 2Θ` pole-exclusion premise if the paper derives pole avoidance:
* change the result denominator to count later commentary:
* delete correct result-adjacent extension proofs:
* redo unrelated Section 3–8 mathematics:
* refactor the entire norm library:
* rewrite all paper proofs to follow the 1970 proof order:
* make broad cleanup changes unrelated to source correctness or Palomar extraction.

Keep the pass focused, but carry that focused task to completion.

---

# Work order

Use roughly this order unless actual dependencies force a different one;

1. verify current source and reported 79/81 state:
2. inspect the reflection/symmetric-sine proof route:
3. implement the three missing unitary/reflection transport lemmas:
4. prove complex ambient unbounded arbitrary-UI `sin 2Θ`:
5. prove/transport the real theorem:
6. add fixed-field source aliases:
7. register both clauses:
8. obtain 81/81 coherent source-clause coverage:
9. audit checker loopholes and regressions:
10. hostile-audit all 29 paper results:
11. fix every additional source-correspondence issue discovered:
12. only then restore 29/29:
13. finish the Section 2 source-facing multi-clause API:
14. finish clean generic `[RCLike]` headline surfaces:
15. construct the policy-valid Palomar Challenge:
16. build the production↔Challenge comparator:
17. build/finish the Palomar Solution:
18. validate import closure, line/byte budgets, and all repository gates:
19. regenerate current documentation:
20. perform the final four-theorem source/production/Palomar hostile comparison.

Do not reorder this so that presentation work masks an unresolved mathematical theorem.

---

# Required final report

When finished, give a concrete report with these sections.

## 1. Mathematical repair

State;

* exact new complex ambient `sin 2Θ` theorem:
* exact new real theorem:
* proof route used:
* transport lemmas added:
* how arbitrary UI norm membership/gauge was handled:
* how full gap scope, including half-infinite cases, was preserved:
* how the exact factor `2` was obtained.

## 2. Certificate

State;

* final source-clause count:
* established/open count:
* final 29-result count:
* whether all 29 hostile reviews pass:
* every additional issue found during the full audit:
* how each was resolved.

## 3. Previously suspicious results

Explicitly state the final status of;

* `S2-tan-theta`:
* `S2-sin-two-theta`:
* `S2-tan-two-theta`:
* `DK-4.2-prop`:
* `DK-8.2-thm`.

For each, distinguish mathematical proof repair from registration/audit repair.

## 4. Checker

Describe;

* final coherent-evidence schema:
* what invalid old configuration it rejects:
* tests added:
* treatment of equivalent gap spellings:
* how scalar coverage is enforced.

## 5. Section 2 API

List;

* all real/complex directed and ambient source endpoints:
* the four generic headline declarations:
* any source-result structures/propositions introduced:
* whether any public theorem still exposes implementation-only capability classes.

## 6. Palomar Challenge

Give exact;

* path:
* imports:
* lines:
* bytes:
* local definition count:
* theorem count:
* dependency audit:
* whether any Challenge symbol comes from DKPS-local or unmerged Tau Ceti code.

## 7. Palomar correspondence/Solution

Explain;

* fixed-field correspondence:
* generic `RCLike` dispatch:
* source-object correspondence:
* whether all four Challenge theorems are fully proved:
* any remaining Palomar policy issue.

## 8. Validation

Give exact commands and results for;

* `lake build`:
* `lake build Challenge`:
* `lake build DavisKahan.Audits.All`:
* source/census checks:
* checker tests:
* Palomar build:
* Challenge line/byte checks:
* import-policy checks:
* trust/axiom checks.

If pre-existing failures remain, list them and demonstrate that they did not regress.

## 9. Final verdict

Choose exactly one;

```text
READY;
29/29 source-faithful, all coherent clauses established,
four full unbounded Section 2 theorems exposed cleanly,
and Palomar Challenge/Solution ready.

PRODUCTION COMPLETE / PALOMAR BLOCKED;
all source mathematics and 29/29 certification complete,
but a specific demonstrated external Palomar dependency/policy issue remains.

NOT COMPLETE;
one or more mathematical/source-correspondence obligations remain open.
```

Do not use `READY` while anything in the hostile review is open.

# Final standard

The target is not merely “the build passes.”

The target is a repository in which a hostile mathematical reviewer can take any one of the 29 Davis–Kahan results, especially the four Section 2 headlines, point to every printed clause, and point to coherent compiler-checked Lean evidence at the same scalar, operator, dimensional, norm, gap, and angle scope.

For Section 2, that same reviewer should then be able to open the Palomar Challenge, read four clean source-shaped `[RCLike 𝕜]` headline theorems, compare them directly with Davis–Kahan, and find no loss of generality introduced for packaging convenience.

Finish that state.


---

# COMPLETION RECORD — 2026-08-31

This brief was worked in full.  The record below is the delivery side of it; the
report it asks for is `dev/davis-kahan-1970-final-report-2026-08-31.md`, in the
nine sections specified above.  Commits: `9ccb2a8a`, `cc824790`, `8d8f2de3`.

## End-state items

| # | requirement | status | where |
| --- | --- | --- | --- |
| 1 | ambient `sin 2Θ` over `ℂ` | **done** | `sinTwoTheta_ambient_unbounded_addBounded_paperUINorm_complex` |
| 2 | the same over `ℝ` | **done** | `…_real` |
| 3 | genuine ambient object, not the directed surrogate | **done** | conclusion on `paperSinTwoAngleOperatorC` / `…R` |
| 4 | arbitrary `PaperUnitaryInvariantNorm` | **done** | in the printed type |
| 5 | unbounded self-adjoint source scope | **done** | `A : H →ₗ.[𝕜] H` |
| 6 | half-infinite configurations preserved | **done** | `FormBoundedSylvesterGap.unitaryConj_left/_right` case on every constructor |
| 7 | ideal membership concluded | **done** | first conjunct of the conclusion |
| 8 | factor exactly `2` | **done** | from `N(H − J H J) ≤ 2 N(H)` |
| 9 | no implementation-only hypothesis | **done** | no capability class, no `FiniteDimensional` |
| 10 | no norm/dimension specialization substituted | **done** | — |
| 11 | 81/81 clauses established | **done** | count unchanged at 81 |
| 12 | hostile audit of every counted result | **done** | `dev/davis-kahan-1970-result-semantic-review-2026-08-31.md` |
| 13 | denominator still 29 | **done** | unchanged |
| 14 | 29/29 advertised only after the audit | **done** | advertised in the same commit as the audit |
| 15 | old Frankenstein composition still rejected | **done** | negative regression test, asserting the diagnosis |
| 16 | scalar, clause, operator, norm, gap and correspondence scope compiler-auditable | **done, strengthened** | four new rules, four new tests |
| 17 | each headline has a source-facing representation of the complete result | **done** | clause aliases for all four; `sinTwoTheta_source_*` certificate |
| 18 | directed and ambient named explicitly | **done** | eight aliases |
| 19 | `sin 2Θ` gains its ambient aliases | **done** | `sinTwoTheta_ambient_complex` / `…_real` |
| 20 | no short name documented as the whole theorem while naming one clause | **done** | docstrings and table corrected |
| 21 | generic `[RCLike 𝕜]` public surface for all four | **NOT DELIVERED — blocked** | `dev/section-two-rclike-endpoint-frontier.md` |
| 22 | fixed-field endpoints retained | **done** | — |
| 23–30 | four-theorem Palomar Challenge, comparator, Solution | **NOT DELIVERED — blocked** | `dev/palomar-section-two-challenge-audit-2026-08-31.md` |
| 31 | Challenge line and byte counts measured | **done** | 95 lines / 4555 bytes for the existing entry; ~350–450 lines projected for a complex-only four-theorem one |
| 32 | concrete Palomar readiness verdict | **done** | §9 of the report |

## The two blocked items, and why

Both are the same missing upstream layer, and it is in the **statement**, not the
proof.  Mathlib reaches a real continuous functional calculus only through
`IsSelfAdjoint.instContinuousFunctionalCalculus`, whose hypothesis is
`[ContinuousFunctionalCalculus ℂ A IsStarNormal]` — a *complex* C⋆-algebra.  This
repository names the real angle operators by complexifying, which a Challenge may
neither import nor inline, and which a generic `[RCLike 𝕜]` statement cannot
reference at all.  So there is nothing to dispatch and nothing to import until a
scalar-generic angle vocabulary exists.  `sin Θ` is the exception in both places
for the same reason: its conclusion is a scalar-generic operator expression.

The earlier reasoning that `RCLike` admits no real/complex dispatch was wrong
about Mathlib and is corrected in the frontier document;
`RCLike.I_eq_zero_or_im_I_eq_one` with `realLinearIsometryEquiv` and
`complexLinearIsometryEquiv` is that dispatch.  It does not help here.

## Standing constraint honoured

Nothing was submitted to or registered with Palomar, and no submission surface
was created in this repository.

## Verdict

`PRODUCTION COMPLETE / PALOMAR BLOCKED`.
