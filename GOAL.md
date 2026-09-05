# Davis–Kahan 1970 — Source-Exact Formalization Completion Goal

## Objective

Finish the Davis–Kahan 1970 formalization so the repository can truthfully claim;

> **Every designated Davis–Kahan result is represented by Lean evidence with the same mathematical statement and scope as the result Davis and Kahan actually prove in the paper.**

The requirement is **statement exactness**, not proof reproduction.

For each designated result, the canonical source-facing theorem must match the paper in;

* hypotheses:
* quantified mathematical objects:
* scalar scope:
* separability and dimension scope:
* bounded versus unbounded operator scope:
* domain assumptions:
* reducing/trial/exact subspace roles:
* spectral-gap location:
* directed-angle orientation:
* residual versus perturbation quantities:
* unitary-invariant norm class and definedness convention:
* constants:
* conclusion.

The Lean proof may use any correct route.

It may;

* prove real and complex cases separately:
* derive one scalar case from the other by complexification or realification:
* invoke stronger internal theorems:
* use different intermediate objects:
* use different lemmas from Davis–Kahan:
* use a completely different argument:
* prove a more general `RCLike` theorem and specialize it:
* prove separate `ℝ` and `ℂ` theorems and optionally wrap them in an `RCLike` theorem.

None of those choices affect source exactness as long as the final source-facing theorem has the paper's statement and does not expose additional hypotheses absent from the paper.

---

# I. What counts as complete

A designated Davis–Kahan result is complete when there is kernel-checked Lean evidence whose **public theorem statement** represents exactly the mathematical result Davis and Kahan state and prove.

A source-exact façade may be a thin wrapper around a much stronger theorem.

For example, all of the following are acceptable;

```text
general arbitrary-Hilbert theorem
        ↓
separable real source façade
```

```text
complex proof
        ↓
real source façade through complexification
```

```text
RCLike theorem
        ↓
ℝ source façade
        ↓
ℂ source façade
```

or;

```text
ℝ proof       ℂ proof
   \           /
    optional RCLike wrapper
```

There is **no requirement** that every result be proved generically over `RCLike` all the way down.

There is **no requirement** that a source façade reproduce the internal proof structure used by another theorem.

A proof such as;

```lean
theorem source_exact_theorem ... ;
    <exact Davis–Kahan statement> ;= by
  exact stronger_internal_theorem ...
```

is completely acceptable if the theorem type is source-exact and the internal theorem supplies everything required.

---

# II. What source exactness does not require

The following are explicitly **not completion requirements**.

## 2.1 Reproducing Davis–Kahan's proof

Do not require the Lean proof to;

* follow the order of the paper's argument:
* use the same intermediate lemmas:
* use the same operator representation:
* use the same continuation argument:
* expose the same proof witnesses:
* visibly compose a particular transport chain in the body of the canonical theorem.

The theorem statement is the contract.

If a checker requires a particular proof-body dependency merely to demonstrate that a known transport was used, remove or narrow that requirement unless the public theorem type itself fails to establish source correspondence.

## 2.2 Maximal scalar generality

Arbitrary `RCLike` results are useful generalizations.

They are not prerequisites for source coverage.

Davis–Kahan's source scope is real and complex Hilbert spaces. Separate exact `ℝ` and `ℂ` theorems are sufficient.

## 2.3 Maximal Hilbert-space generality

Arbitrary-Hilbert-space versions are useful stronger results.

They are not substitutes for source-exact façades when Davis–Kahan assume separability, and finishing every arbitrary-Hilbert generalization is not required once the exact source theorem exists.

## 2.4 Formalizing every mathematical sentence in the paper

The completion denominator is the designated set of Davis–Kahan results.

Do not make completion depend on formalizing;

* proof steps:
* examples used only to explain a theorem:
* historical remarks:
* open questions:
* externally cited facts:
* commentary:
* sharpness discussions:
* asymptotic commentary:
* later optional extensions:
* every mathematical statement appearing in prose.

Such results may be useful supplemental formalizations. They are not blockers unless they are themselves part of a designated Davis–Kahan result or are necessary to interpret the actual scope of one.

Existing supplemental formalizations should be preserved.

## 2.5 Building broad infrastructure for its own sake

Do not require a general unbounded-operator, Riesz-projection, holomorphic-functional-calculus, or continuation library merely because one proposed proof route would use it.

Start from the exact theorem that remains to be proved.

Add the smallest reusable mathematical lemmas needed to prove it.

If an apparently large infrastructure task collapses to a short argument using existing machinery, use the short argument.

---

# III. Result denominator

The working denominator remains the repository's 29 designated Davis–Kahan result obligations unless a direct source audit establishes that the inventory itself is wrong.

The denominator should contain results Davis and Kahan actually state and establish in the paper.

Do not add a new obligation merely because a nontrivial mathematical assertion appears in prose.

Likewise, if a transcription or reconstruction contains an assertion that is not actually a Davis–Kahan proved result, do not force Lean to prove it merely to preserve an inventory count.

A false or corrupted source-transcription assertion may be;

* formally refuted:
* retained as a fidelity/audit record:
* clearly distinguished from proved Davis–Kahan results.

The public claim must accurately distinguish proved source results from any formally refuted transcription or source issue.

---

# IV. Primary source authority

The ultimate source is;

Chandler Davis and W. M. Kahan,
*The Rotation of Eigenvectors by a Perturbation. III*,
SIAM Journal on Numerical Analysis 7(1), 1970, pp. 1–46.

DOI;

```text
10.1137/0707001
```

Repository transcriptions, distilled literature files, inventories, statement maps, comments, and earlier review conclusions are aids.

They are not authorities over the original paper.

When there is disagreement or ambiguity, inspect the original source.

---

# V. Exact source façades

Canonical source evidence should be deliberately source-shaped.

## 5.1 Source hypotheses

The canonical theorem must not require assumptions absent from Davis–Kahan merely because the proof needs them.

In particular, do not expose caller-supplied;

* correspondence witnesses:
* partial isometries that Davis–Kahan derive:
* crossed-defect equivalences imported from a later theorem:
* tangent representatives:
* approximation-number transports:
* functional-calculus implementation capabilities:
* proof-engineering typeclasses.

Such data may be constructed internally.

## 5.2 Source hypotheses that are redundant in Lean

If Davis–Kahan explicitly work under a standing assumption such as separability, retain that scope on the exact source façade even when the underlying Lean theorem proves a stronger result without it.

The exact façade exists to identify the source theorem.

The stronger theorem should remain separately available.

## 5.3 Real and complex scope

For results applying to both real and complex Hilbert spaces, source coverage may consist of;

```text
exact real theorem
exact complex theorem
```

An arbitrary-`RCLike` theorem is optional stronger evidence.

There is no requirement that the real and complex theorems have isomorphic internal proofs.

## 5.4 Finite-dimensional versus infinite-dimensional scope

Match the scope of the particular source result.

If a clause is explicitly finite-dimensional, its exact source façade may remain finite-dimensional.

Do not require an infinite-dimensional generalization before declaring that clause complete.

If a result is arbitrary-dimensional in the paper, a finite-dimensional specialization is not sufficient.

## 5.5 Unbounded operators

Where a designated theorem inherits Davis–Kahan's unbounded self-adjoint scope, the exact theorem must support that scope.

A bounded theorem is not a source-exact substitute.

This applies in particular to the Section 8 results to the extent that their printed statements inherit the Section 2 hypotheses without imposing a bounded-\(A\) restriction.

The implementation route used to prove those unbounded statements is unrestricted.

---

# VI. Literal unitary-invariant norm scope

Davis–Kahan quantify over arbitrary normalized unitary-invariant norms with the paper's ideal/definedness behavior.

The repository now has;

```text
NormalizedUnitaryInvariantNorm
```

as the source-facing abstraction.

Preserve it.

Canonical results whose source statement quantifies over arbitrary unitary-invariant norms should quantify over this literal source abstraction, or another transparently equivalent source abstraction if the design is later improved.

Existing;

```text
SymmetricNormingFunction
KyFanDominantIdealFamily
```

theorems remain valuable analytic/general results.

They may be used internally through Fan dominance.

They are not substitutes for the source-facing norm quantifier.

Do not add a UIN parameter to a theorem clause that does not have one in Davis–Kahan.

Do not require Calkin-algebra formalization or examples merely to justify this abstraction.

---

# VII. Internal representations

Different internal representations are allowed.

Examples include;

```text
genericCosineBlock
sinTwoThetaIdealBlock
reflection pairs
Ky Fan families
approximation-number sequences
complexifications
bounded block representatives
```

If the **public source façade itself** states the result using the Davis–Kahan mathematical objects, Lean's proof may freely pass through such representations internally.

A separate globally registered correspondence theorem is not required for every intermediate proof step.

A compiled correspondence becomes a source-exactness requirement when the canonical public theorem substitutes an internal object for the source object and asks the reader to regard them as equivalent.

Prefer avoiding that problem by making the final façade speak directly in source terms.

---

# VIII. Preserve the repairs already established

The following historical defects must not regress;

* directed `sin 2Θ₀` uses residual `R`, not full perturbation `H`:
* directed `sin 2Θ₀` uses the correct ordered trial-side angle:
* Theorem 8.2 uses the same correct directed orientation:
* ambient `sin 2Θ` places the gap on the correct `Λ₀, Λ₁` blocks of `A + H`:
* Theorem 3.1 states the actual source angle-multiplicity invariant:
* Corollary 3.1 permits the source's independent zero multiplicities:
* Theorem 3.1 derives `J₀` rather than requiring it from the caller:
* source ambient-dimension conditions are propositions rather than caller-chosen equivalences:
* condition `(3.5)` has a compiled relationship to the source Hilbert-dimension condition where needed:
* Section 2 tangent results do not import condition `(3.5)` as an extra public hypothesis:
* source tangent semantics correctly handle definedness/poles:
* Theorem 5.1 has its source Banach/norm scope:
* Theorem 5.2 real and complex versions use the printed ordered semibounds:
* source-facing theorem types do not expose implementation capability classes absent from the paper.

Keep the existing focused regression module and targeted tamper checks where they cheaply protect these facts.

Do not replace them with a much larger generic verification framework.

---

# IX. Current completed infrastructure

As of the current 2026-09-05 implementation state, preserve the completed work rather than rebuilding it;

* `NormalizedUnitaryInvariantNorm` and its Fan-dominance bridge:
* source UIN façades already added across Section 2 and later results:
* exact separable real/complex façades already completed:
* machine-readable distinction between canonical source evidence and generalizations:
* hostile-review regression invariants:
* targeted registration tamper tests:
* existing unbounded self-adjoint resolvent and spectral-gap machinery:
* the completed coercive/inverse result used for Section 8.1:
* the unbounded Section 8.1 spectral-repulsion half already proved.

Do not reopen any of these merely to obtain a more uniform internal API unless a source-exactness defect is found.

---

# X. Remaining source-exactness blockers

The critical path should now be narrow.

## 10.1 Directed real `S2-tan-two-theta`

Provide the missing exact real source façade.

The current difficulty is internal scalar transport; the tangent corner is represented on a complexification while the residual data are real.

Solve that transport in whichever way is smallest and correct.

Possible approaches include;

* transporting the literal UIN object through complexification:
* proving a real source theorem by applying the complex theorem and transporting the resulting inequality:
* introducing a narrowly scoped heterogeneous norm comparison.

Do not require a generic `RCLike` solution if separate real and complex source theorems close the source statement.

### Acceptance

The public real theorem has exactly the Davis–Kahan assumptions and conclusion.

No extra transport witness is supplied by the caller.

## 10.2 Directed complex `S2-tan-two-theta`

A source-exact façade already exists according to the current progress record.

The existing checker requirement that the **primary theorem itself visibly compose a five-step transport chain** is not a source-exactness requirement.

Review the compiler-expanded façade type.

If the public theorem;

* has the correct source assumptions:
* uses the correct directed angle:
* quantifies over the correct norm:
* has the correct RHS and constant:
* exposes no extra hypothesis:

then the result is source-exact even if its proof delegates to another theorem.

Revise or remove any gate that rejects the theorem only because of proof-body structure.

Retain a transport-chain regression check only if it protects an actual mathematical statement invariant.

## 10.3 Unbounded Theorem 8.1

The canonical Theorem 8.1 must match the source's inherited unbounded self-adjoint scope.

Do not prescribe in advance how to prove it.

Existing progress already supplies;

* the required coercive/inverse ingredient:
* the unbounded spectral-repulsion half.

The remaining open mathematical point is the quarter-acute conclusion represented by the current `isQuarterAcute_of_orderedFormGap` obstruction.

Work directly on that implication.

### 10.3.1 What that implication should actually say (finding, 2026-09-05)

Reading the printed statement changes this target, and the change is the whole
difficulty.

**The paper's conclusion is `Θ ≤ π/4`, non-strict**, and it is an *iff* with the
spectral placement `Λ₁ ≥ α + δ`, `Λ₀ ≤ α`. The proof it gives is scalar and
pointwise: equation (8.2),

```text
x₀* B* y₁ (tan θ − cot θ) = y₁* A₁ y₁ − x₀* A₀ x₀ ≥ δ > 0,
```

"excludes `θ = π/4` and then `θ > π/4`" — i.e. **every principal angle is
strictly below `π/4`, so their supremum is at most `π/4`.**

**The repository currently concludes the strictly stronger statement.**
`IsQuarterAcute U V` unfolds to `subspaceGap U V < √2/2` and
`maximalAngle U V < π/4` is the same thing through `arcsin`: both are strict on
the *supremum*, not per angle. That is more than Davis and Kahan claim.

**And the supremum-strict form is what does not survive to unbounded scope.**
The bounded proof (`isQuarterAcute_of_orderedFormGap`) ends with

```text
α = δ / (1 + ‖C^(1/2)‖²) = δ / (1 + ‖C‖),      C = K (A + H − c),
```

and every later step consumes that `α` uniformly. As `‖A‖ → ∞` it goes to zero.
This is not a formalization artifact: in the commuting model `W = diag(wₙ)`,
`C = diag(cₙ)`, the hypothesis is exactly `re wₙ ≥ δ/cₙ`, so with `cₙ → ∞` the
angles may increase to `π/4` without reaching it. An orthogonal sum of planar
blocks with a fixed gap `δ` and outer scale `cₙ → ∞` realises that: each block
satisfies the bounded theorem, the sum has unbounded `A`, and
`subspaceGap = √2/2` exactly. `IsQuarterAcute` fails there; `Θ ≤ π/4` holds.

**So the target is the printed statement**, and it should be stated the way the
paper proves it:

```text
every principal angle < π/4        (pointwise strict)
    ⟹  subspaceGap U V ≤ √2 / 2   (supremum, non-strict)
    ⟹  maximalAngle U V ≤ π/4
```

Two consequences for the plan:

* Do not try to lift `isQuarterAcute_of_orderedFormGap` as stated. Its conclusion
  is stronger than the source and is not available unbounded.
* The bounded `IsQuarterAcute` result stays, as a genuinely stronger theorem
  under the extra hypothesis that `A` is bounded, and should be registered as a
  generalization rather than deleted.

The Lyapunov structure survives the change of scope and is the place to start.
Writing `G = C⁻¹` (bounded by §6.2, `‖G‖ ≤ δ⁻¹`, positive, injective), the
identity `C W + W* C = 2B` becomes, after multiplying by `G` on both sides, a
statement about bounded operators only:

```text
W G + G W* = 2 G B G ≥ 2 δ G²,      and      W G = Y − S
```

with `Y = G B G ≥ δ G²` self-adjoint and `S = G J H G` skew-adjoint (`H` is
bounded, and `J H = − H J`). Since `W` is unitary, `|W G| = G`, so `W` is the
polar unitary of an accretive operator whose modulus is `G`. The conclusion
`W + W* ≥ 0` — which is exactly `Θ ≤ π/4` — is then the bounded question

> if `G ≥ 0` is injective and `W G + G W* ≥ 0` with `W` unitary, is
> `W + W* ≥ 0`?

This simplifies further, and the simplified form is the right handoff.
Conjugating the hypothesis by the unitary `W` gives a second one,

```text
W* (W G + G W*) W = G W + W* G ≥ 0,
```

and adding the two collapses `W` into its real part: writing `X = W + W*`,

```text
X G + G X ≥ 0,        G ≥ 0 injective,       X self-adjoint.
```

`Θ ≤ π/4` is exactly `X ≥ 0`. So the whole unbounded quarter-angle question is
the classical Lyapunov implication

> `X` self-adjoint, `G ≥ 0` injective, `X G + G X ≥ 0`  ⟹  `X ≥ 0`?

**For invertible `G` this is a theorem**, and its proof is two lines:
`G^(−1/2)(XG + GX)G^(−1/2) = Z + Z*` with `Z = G^(1/2) X G^(−1/2)`, so `Z` is
accretive; `Z` is similar to `X`, so they have the same spectrum; and a
self-adjoint operator with spectrum in the closed right half-plane has spectrum
in `[0, ∞)`. Invertible `G` is exactly bounded `A`, which is why the bounded
theorem is easy.

For `G` merely injective the similarity is unbounded and spectra need not agree.
What is settled: the implication holds whenever `X` has an actual eigenvector for
a negative eigenvalue (`2λ⟪Gv,v⟫ ≥ 0` with `⟪Gv,v⟫ > 0` forces `λ ≥ 0`), and
hence in finite dimensions and for any `X` with pure point spectrum. What is open
is the purely-continuous negative spectrum case, where approximate eigenvectors
`vₙ` may have `⟪G vₙ, vₙ⟫ → 0` fast enough to absorb the defect. Settle that
question -- either way -- and unbounded Theorem 8.1's headline conclusion
follows or the statement needs a further hypothesis.

Candidate proof routes recorded in the repository may be useful, but none is mandatory.

In particular, do not build a large general unbounded form calculus unless the theorem actually needs it.

### Acceptance

The final source-facing real and complex Theorem 8.1 evidence;

* inherits the paper's actual unbounded assumptions:
* has the paper's separability/dimension scope:
* matches each finite-dimensional versus general clause exactly:
* exposes no proof-specific assumptions.

Any bounded or arbitrary-Hilbert variants remain separate useful theorems.

## 10.4 Unbounded Theorem 8.2

The canonical Theorem 8.2 must likewise match the source's inherited unbounded scope.

There are two public branches to protect separately.

### Perturbation branch

Prove the source theorem under the printed perturbation-size hypothesis.

### Residual branch

Prove the source alternative under the printed residual-size hypothesis.

The residual theorem must **not** acquire the perturbation-size hypothesis merely because a convenient proof route uses it.

### Implementation policy

Start from the source-exact theorem signature.

Then inspect what is actually missing.

The current plan's proposed sequence;

```text
general unbounded resolvent
second resolvent identity
gap stability
general Riesz projection
continuation API
Lipschitz spectral branch
```

is one possible route.

It is not itself a completion requirement.

Existing resolvent machinery should be reused first.

If a shorter argument using;

* `specRange`:
* existing spectral-measure machinery:
* a direct projection estimate:
* complexification:
* an existing continuation theorem:
* a bounded transform:
* another standard self-adjoint reduction

proves the source theorem, prefer that route.

Do not require the bounded continuation API to become a specialization of a new general API.

### Unequal-dimension remark

Do not make a later unequal-dimension extension a blocker for Theorem 8.2 unless source inspection shows that it is actually part of the designated theorem statement or is independently one of the designated results.

If it is a subsequent extension remarked upon outside the theorem, retain it as supplemental work.

---

# XI. Stronger results

Preserve stronger results that already exist.

Examples include;

* arbitrary Hilbert space:
* arbitrary `RCLike`:
* broader gap hypotheses:
* more general residual data:
* `SymmetricNormingFunction`:
* `KyFanDominantIdealFamily`:
* stronger domain/operator formulations.

Register them as generalizations where the current schema supports that distinction.

However;

> **Completion of every stronger API is not required for source completion.**

Do not delay the source-exact result in order to finish a generic wrapper.

Do not manufacture generalizations solely to populate the inventory.

---

# XII. Supplemental source assertions

Supplemental results may include;

* optimality of constants:
* equality examples:
* simultaneous direct-sum equality constructions:
* first-order asymptotics:
* later scope extensions:
* other nontrivial prose assertions.

Preserve supplemental formalizations already completed.

Continue them later if useful.

They are **outside the critical path for 29/29 designated-result source exactness** unless source inspection demonstrates that a particular assertion is actually part of one of the designated theorem statements.

The public reporting should make this distinction explicit;

```text
Designated Davis–Kahan results;
    source-exact status

Supplemental formalization;
    additional paper assertions, examples, sharpness results,
    extensions, and generalizations
```

Do not require every supplemental source atom to be accepted before declaring the designated theorem formalization complete.

---

# XIII. Hostile source-first review

Before the final certification pass, perform a fresh hostile review of the designated result set.

The purpose is to detect;

```text
Lean proves a true theorem
but it is not actually the Davis–Kahan theorem.
```

The reviewer should use the original paper as authority.

For each designated result;

1. identify the exact printed result and any inherited standing assumptions:
2. inspect the compiler-expanded canonical source theorem:
3. compare the mathematical hypotheses:
4. compare scalar scope:
5. compare separability and dimension scope:
6. compare bounded/unbounded scope and domains:
7. compare source mathematical objects and their roles:
8. compare which operator carries each gap hypothesis:
9. compare directed-angle ordering:
10. compare residual versus perturbation quantities:
11. compare UIN norm scope and definedness:
12. compare constants:
13. compare conclusions:
14. check that no proof witness or implementation capability has leaked into the public hypotheses.

The decisive question is;

> **Does this Lean theorem state the same mathematical result that Davis and Kahan state, at the same scope, without adding assumptions?**

Do **not** ask;

> Does the Lean proof follow Davis and Kahan's proof?

That is not the review target.

## Representation review

If the public theorem directly uses the source mathematical object, internal proof representations do not need independent source-certification.

If the public theorem substitutes another object for the source object, require a compiled equivalence/correspondence sufficient to justify that substitution.

## No automatic reopening for stronger mathematics

Do not reopen a row merely because;

* the underlying theorem is stronger:
* its proof uses arbitrary Hilbert spaces:
* the proof is generic over `RCLike`:
* the proof uses an internal block representation:
* the source façade is only a short wrapper:
* the argument differs from the paper.

Reopen only for a difference in the mathematical public statement or source scope.

---

# XIV. Certification and regression policy

During implementation use lightweight, targeted validation.

Prefer;

* targeted module builds:
* `#check` / compiler-expanded theorem signatures:
* relevant audit modules:
* affected statement pins:
* narrow inventory checks:
* targeted tamper tests.

Do not repeatedly run expensive comparator or clean-certification suites when they do not answer the semantic question being worked on.

Do not run `lake clean`.

Do not delete `.lake`.

The existing historical-regression checks should continue to protect known failures such as;

```text
R ↔ H
P/Q orientation
wrong gap operator
bounded-for-unbounded substitution
complex-only-for-real-and-complex
wrong UIN abstraction
generic block replacing source angle
caller-supplied proof witness
extra Section 2 hypotheses
finite specialization replacing general source result
```

A tamper test should enforce a statement-level invariant.

Do not require a particular theorem's proof body to invoke a named helper unless that dependency is itself necessary to make the public mathematical claim valid.

---

# XV. Final expensive certification

Run the expensive final certification only after;

* all designated source façades exist:
* the known Section 2 scalar gap is closed:
* Theorem 8.1 is source-exact at unbounded scope:
* Theorem 8.2 is source-exact at unbounded scope:
* the fresh 29-row hostile source review finds no open statement mismatch.

Then;

1. freeze the source/inventory state:
2. ensure the working tree is clean:
3. run the normal build:
4. run source audit aggregates:
5. run `Challenge` where still part of the release gate:
6. run declaration-drift checks:
7. run statement pins:
8. run the result inventory and source census:
9. run statement-map/coherence checks:
10. run the targeted tamper suite:
11. run comparator/canonical-evidence checks:
12. run the clean release certification once if required by the release process:
13. verify compiler-probed declarations resolve:
14. verify there are no unexpected production warnings:
15. record the final source/certificate state.

Do not repeatedly pay this cost during ordinary theorem development.

If the final pass reveals a semantic defect, fix the defect and rerun the checks affected by it, followed by a new final release pass.

---

# XVI. Current critical path

Given the current repository state, prioritize work in this order;

## 1. Fix the directed complex `tan 2Θ` certification policy

Inspect the existing source façade's expanded theorem type.

If it is exact, stop requiring a prescribed transport chain in the proof body.

This may remove a reported gap without any new mathematics.

## 2. Add the directed real `tan 2Θ` source façade

Solve only the real/complex norm transport necessary to obtain the exact real statement.

Do not turn this into a requirement for a fully generic scalar API.

## 3. Finish unbounded Theorem 8.1

Use the already completed coercive inverse and spectral-repulsion work.

Concentrate on the genuinely missing quarter-acute implication and then expose the exact source theorem.

## 4. Finish unbounded Theorem 8.2

Write the final source theorem types first.

Determine the smallest missing operator-theoretic ingredients from those targets.

Do not assume the large Riesz/continuation roadmap is necessary until the proof forces it.

Protect the residual alternative from accidental extra perturbation hypotheses.

## 5. Fresh hostile review of all designated results

Review source statements against compiler-expanded theorem types.

Fix only actual source mismatches.

## 6. One final certification pass

After semantic closure, run the expensive gates once.

---

# XVII. Definition of done

The Davis–Kahan designated-result formalization is complete when all of the following hold;

* every designated Davis–Kahan result has canonical Lean evidence at its actual source scope:
* every real/complex result has source coverage for both fields, whether by separate proofs, transport, or specialization:
* canonical Hilbert-space façades expose the paper's separability scope where applicable:
* finite versus infinite-dimensional scope matches each printed result:
* bounded versus unbounded scope matches each printed result:
* every relevant UIN-quantified theorem uses the literal source UIN abstraction at its public boundary:
* no canonical source theorem asks the caller for a hypothesis or proof witness absent from the paper:
* source objects, gap locations, ordered angles, residuals, constants, and conclusions agree with the paper:
* Theorems 8.1 and 8.2 cover their actual inherited unbounded scope:
* the exact/stronger distinction remains visible in the census:
* a fresh source-first review finds no material statement mismatch:
* the final certification pass succeeds.

The following are **not** prerequisites;

* reproducing Davis–Kahan's proofs:
* completing every `RCLike` generalization:
* completing every arbitrary-Hilbert generalization:
* building a predetermined unbounded Riesz/continuation architecture:
* formalizing every sharpness/example/asymptotic assertion in the paper:
* formalizing every mathematical prose sentence:
* making every stronger theorem part of a perfectly uniform API.

---

# XVIII. Final public claim

When the conditions above are satisfied, the repository may claim;

> **The designated Davis–Kahan 1970 results have been formally resolved in Lean at the mathematical scope of their original statements, including the applicable real and complex, separable-Hilbert-space, unbounded-operator, and arbitrary normalized unitary-invariant norm scope. Stronger generalizations are recorded separately and are not used to conceal missing source-exact evidence.**

If the designated inventory contains a source or transcription assertion that is formally refuted rather than proved, state that separately and do not collapse it into the phrase “all theorems proved.”

Supplemental sharpness, examples, asymptotics, extensions, and stronger APIs may be described separately.

The formalization claim is about **the Davis–Kahan results themselves**.

That is the finish line.
