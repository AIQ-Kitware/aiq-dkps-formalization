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

**Status, corrected 2026-09-06.**  The sentence that used to stand here — "the
remaining open mathematical point is the quarter-acute conclusion" — is out of
date.  That conclusion is proved: §10.3.1 and §10.3.2 record the reading of the
printed statement and the Lyapunov route, and
`maximalAngle_le_pi_div_four_of_orderedFormGap_unbounded_printed` and
`subspaceGap_le_of_orderedFormGap_unbounded_printed` are the unbounded angle and
projector-gap conclusions in the paper's own orientation.  The unbounded
spectral-repulsion half
(`notMem_spectrum_addBounded_of_offDiagonal_form_gap`) and the coercive/inverse
ingredient (§6.2) were already there.

**Branch existence is done, 2026-09-06.**
`Section8/Theorem81UnboundedBranch.lean` supplies, at the printed hypotheses and
at unbounded scope, the branch `Q = specRange (A + H) (Iic α)` with all three
printed facts about it: it reduces `A + H`, it carries `Λ₀ ≤ α` and
`Λ₁ ≥ α + δ`, and `Θ(P, Q) ≤ π/4`
(`theorem8_1_canonicalBranchUnbounded_printed`).  The two form bounds are the
half-line energy bounds of the spectral measure applied through a one-sided
limit — a vector of the branch has no spectral mass above `α`, so its form is at
most `c ‖x‖²` for *every* `c > α` — with the open gap `(α, α + δ)` removed by the
already-proved unbounded repulsion.

**The characterization's forward direction is done too, 2026-09-06.**
`theorem8_1_maximalAngle_le_of_spectrumIn_unbounded` takes the printed *spectral*
placements — `Λ₀ ⊆ (−∞, α]`, `Λ₁ ⊆ [α + δ, ∞)`, and the same for `A` across `P` —
and concludes `Θ ≤ π/4` at unbounded scope.  The bridge is
`re_inner_le_of_reducingRestriction_realSpectrum_subset_Iic` and its dual: a point
outside the closed half-line is a resolvent point, so its spectral projection
vanishes, and the half-line energy bounds of the spectral measure give the form
bound the quarter-angle theorem wants.

**Part (i) is done, 2026-09-06.**
`theorem8_1_upperCompressionRepulsion_unbounded` and its lower-block dual give
part (i) in its form reading: the `α`-shifted energy of a domain vector is at
most that of its component in the branch's complement.  The proof is
`re_inner_split_of_reduces` — a reducing subspace splits the energy, the cross
terms vanishing by invariance — plus the branch's own ordered form bound.
Nothing about `P` is used, so it holds on the whole domain; the paper's `Pᗮ` is
only where it is read.

**Parts (ii) and (iii) are not unbounded obligations at all.**  Measured against
the source, 2026-09-06: the paper prints (ii) *"in finite dimensions … with the
analogous lower-block statement and natural infinite-dimensional extensions"* and
(iii) *"for every symmetric gauge function `Φ` in finite dimensions"*.  Part (i),
by contrast, carries no dimension qualifier and so inherits the ambient unbounded
scope.  So the existing finite/bounded evidence for (ii) and (iii) is **at** the
printed scope, and the dimension-free approximation-number form already
registered covers (ii)'s extension remark.  §XVII's "finite versus
infinite-dimensional scope matches each printed result" is satisfied for them.

### 10.3.3 The converse half: closed (2026-09-06)

**Both halves of Theorem 8.1's printed *iff* are now proved at unbounded scope.**
`theorem8_1_maximalAngle_le_iff_orderedFormGap_unbounded` is the printed
equivalence; `theorem8_1_eq_canonicalBranchUnbounded_of_maximalAngle_le` is the
uniqueness of the branch that carries its `only if` half.

An earlier revision of this section argued the converse was an open mathematical
question.  That argument was wrong, and the error is worth recording because it is
the kind that closes a route prematurely.

*The wrong step.*  It assumed the pair `(P, Q)` — `Q` the canonical branch —
supplies only the non-strict `Θ ≤ π/4`, on the grounds that the strict bounded
statement `IsQuarterAcute P Q` costs the constant `δ/(1 + ‖C‖)`, which degenerates
as `‖A‖ → ∞`.  With only non-strict bounds on both pairs a nonzero
`u ∈ M ∩ Qᗮ` is forced to make angle *exactly* `π/4` with `P`, and the bounded
proof's contradiction becomes a consistent configuration.

*What was actually available.*  The degenerating constant is the price of a
**uniform** bound.  The uniqueness argument never uses one: it tests a single
vector at a time, and **pointwise** strictness is enough.  Pointwise strictness was
already inside the unbounded quarter-angle proof and was being thrown away.
`reflectionProduct_form_nonneg_of_orderedFormGap_unbounded` reached
`0 ≤ ⟪(K J + J K) y, y⟫` by discarding the `δ‖G y‖²` margin that the coercivity
`hWG` supplies; retaining it gives `⟪(X G + G X) y, y⟫ ≥ 2δ(‖G y‖² + ‖G (W y)‖²)`,
which is strictly positive for `y ≠ 0` because `G` is injective.  A positive
operator whose form vanishes at `u` is orthogonal to the whole range of `X` at `u`
— an elementary one-variable argument on `re⟪X(v + t u), v + t u⟫` — so
`⟪X u, u⟫ = 0` would kill that margin at `v = G u`.  Hence `⟪X u, u⟫ > 0` for every
`u ≠ 0`, i.e. `‖P_P u − P_Q u‖ < ‖u‖/√2` pointwise:
`norm_starProjection_sub_sq_lt_of_orderedFormGap_unbounded_printed`.

No uniform bound follows, and none is claimed: `‖G y‖` has no positive lower bound
on the unit sphere when `A` is unbounded.  That is exactly consistent with the
paper printing only the non-strict `Θ ≤ π/4` as its conclusion.

*The second ingredient.*  `P_M` commutes with `P_Q`, so `M` splits along `Q` and
the two trivial crossed intersections `M ∩ Qᗮ = 0`, `Q ∩ Mᗮ = 0` give `M = Q`.
The commutation is `LinearPMap.specProjection_apply_of_unitary_intertwines`: a
unitary preserving `dom B` and commuting with `B` commutes with every
`specProjection`, since `cayley_intertwines` carries the relation to the Cayley
transform and `BorelCalculus.borelCalculus_comp_val_of_intertwines` carries it
through the Borel calculus.  `SeparatedIntertwiner` recorded the Borel step as
open; it is open for a *general bounded* intertwiner, and was already available for
a **unitary** one, which is the only case a reducing subspace needs — a subspace
reduces `B` exactly when its reflection is a unitary commuting with `B`.

*The real endpoints, and the promotion.*  `Theorem81UnboundedReal.lean` gives the
real siblings of every unbounded Section 8 endpoint — branch existence, the
printed `iff`, uniqueness, and part (i) — by complexification.  The branch is not
transported: `TauCeti.LinearPMap.realSpecRange` already descends the complex
spectral projection, so the real branch is defined directly and
`complexifySubmodule_realSpecRange` says the two agree.  Hypotheses go up
(`re_inner_complexifyReal_le_of_forall_mem`, `isOddFor_complexifySubmodule`,
`reducesSubspace_complexifyReal`) and conclusions come down — form bounds by
evaluating on the real copy, the angle by `subspaceGap_complexifySubmodule`, the
branch identity by injectivity of `complexifySubmodule`.

With complex and real unbounded witnesses for every clause of Theorem 8.1 that
inherits ambient scope, DK-8.1-thm's canonical evidence moved to them on
2026-09-06; the bounded declarations that were canonical are retained as
registered specializations, and parts (ii) and (iii) keep their
finite-dimensional evidence, which is the source's own restriction.  The
promotion was re-reviewed at compiler-printed types and found one defect, now
repaired: four of the unbounded theorems carried both `IsSelfAdjointOperator Hop`
and `IsSelfAdjoint Hop` in the public type — two spellings of one hypothesis.

*What the paper does, for the record.*  Equations (8.1)–(8.2) exclude `θ = π/4` via
`x₀^* B^* y₁ (tan θ − cot θ) = y₁^* A₁ y₁ − x₀^* A₀ x₀ ≥ δ > 0`, whose left side
vanishes at `θ = π/4`.  That is the canonical-angle (CS) decomposition.  The route
above reaches the same exclusion through the Lyapunov positivity of `K J + J K`
instead, and never builds a CS decomposition for the unbounded pair.

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

**The implication is true for merely injective `G`, and the proof is short.**
It does not need `G` to be invertible anywhere; it needs `X` to be invertible on
the piece where it is negative, which is free.

Let `β > 0` and let `E` be the spectral projection of `X` for `(−∞, −β]`. `E`
commutes with `X`. Compress everything to `ran E`: for `v ∈ ran E`, `X v ∈ ran E`,
so

```text
⟪(X G + G X) v, v⟫ = 2 re ⟪G v, X v⟫ = 2 re ⟪G_E v, X_E v⟫ ≥ 0,
```

where `X_E = X|ran E` and `G_E = (E G E)|ran E`. Now `A := −X_E ≥ β` is positive
**and invertible on `ran E`**, and the displayed inequality is `A G_E + G_E A ≤ 0`.
Conjugating by `A^(−1/2)` — legitimate, `A` is invertible here —

```text
Z + Z* ≤ 0,        Z := A^(1/2) G_E A^(−1/2),
```

so `Z` has numerical range in the closed left half-plane, hence spectrum there.
`Z` is similar to `G_E`, so `spectrum G_E ⊆ {re ≤ 0}`; but `G_E ≥ 0`, so
`spectrum G_E ⊆ [0, ∞)`. Therefore `spectrum G_E = {0}`, and a positive operator
with spectral radius `0` is `0`.

That contradicts injectivity: for `0 ≠ v ∈ ran E`,
`⟪G_E v, v⟫ = ⟪G v, v⟫ = ‖G^(1/2) v‖² > 0`. Hence `ran E = 0`, so `X ≥ −β`, and
`β > 0` was arbitrary: `X ≥ 0`. ∎

The invertibility that the bounded proof got from `‖C‖ < ∞` is recovered from the
*other* operator — `X` is bounded below by `β` on exactly the subspace where the
argument runs — which is why nothing degenerates.

### 10.3.2 What to build

**The reusable theorem is done, 2026-09-05.**
`TauCeti.ContinuousLinearMap.nonneg_of_lyapunov_nonneg` in
`ForTauCeti/Analysis/InnerProductSpace/LyapunovPositivity.lean` is exactly

```text
X self-adjoint, G ≥ 0 injective, X G + G X ≥ 0  ⟹  0 ≤ X
```

axiom-clean, with the two supporting theorems it needed:
`spectrum_re_nonpos_of_dissipative` (a dissipative operator has spectrum in the
closed left half-plane, by the contrapositive of `isUnit_of_coercive`) and
`eq_zero_of_anticommutator_nonpos` (the classical invertible case). The
compression to the spectral subspace `X ≤ -β` uses the existing
`boundedPVM` half-line form bounds, so no new spectral machinery was built.

**The projector bridge at the other end is also done, 2026-09-05.**
`reflectionProduct_add_swap_eq` states `K J + J K = 2 − 4 (P_U − P_V)²` as a
standalone theorem, and

```text
subspaceGap_le_of_reflectionProduct_form_nonneg
maximalAngle_le_pi_div_four_of_reflectionProduct_form_nonneg
```

take `K J + J K ≥ 0` to `‖P_U − P_V‖ ≤ √2/2` and to `Θ ≤ π/4`. No constant
appears in either, which is exactly why they survive to unbounded scope where
`isQuarterAcute_of_orderedFormGap`'s strict bound does not.

**What is left is the middle.**  Both ends are built; the remaining work is to
produce the hypothesis of the bridge from the unbounded ordered form gap:

1. From §6.2, `C = K (A + H − c)` has a bounded inverse `G` with `‖G‖ ≤ δ⁻¹`.
   Show `0 ≤ G` (from `⟪G y, y⟫ = ⟪G y, C (G y)⟫ ≥ δ ‖G y‖²`) and `G` injective
   (`G y = 0 ⟹ y = C (G y) = 0`).
2. The coercivity `re ⟪W x, C x⟫ ≥ δ ‖x‖²` on `dom A`, substituted at `x = G y`,
   gives `W G + G W* ≥ 0`.
3. Conjugating by `W` gives `G W + W* G ≥ 0`; adding, with `X = W + W*`,
   `X G + G X ≥ 0`.
4. `nonneg_of_lyapunov_nonneg` gives `0 ≤ X`, and the bridge finishes.

Do not lift the bounded `IsQuarterAcute` statement; keep it as the stronger
bounded theorem it is.

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

### The short route does not exist (correction, 2026-09-05)

An earlier finding here claimed Theorem 8.2's acute conclusion is Theorem 8.1's
`Θ ≤ π/4` plus the double-angle bound, and listed "derive the ordered form bounds
Theorem 8.1 wants from Theorem 8.2's printed `SpectrumIn` hypotheses" as an
assembly step. **That is wrong.** The two theorems inherit different hypothesis
sets from Section 2:

* Theorem 8.1 assumes *the hypotheses of the `tan 2θ` theorem*, which include the
  strong off-diagonal hypothesis `H₀ = H₁ = 0`;
* Theorem 8.2 assumes *the hypotheses of the `sin 2θ` theorem*, which include no
  off-diagonality at all.

So Theorem 8.1 is simply unavailable at Theorem 8.2's hypotheses, and no
translation of spectral containments into form bounds changes that. The closed
branch has to be established by the paper's own connectedness argument.

### How far the static route actually reaches

Write `γ = ‖H‖`, `κ = 2γ/δ < 1`. The printed estimate `δ‖sin 2Θ‖ ≤ 2‖H‖` gives
the dichotomy

```text
g ≤ σ₋(κ) = sin(½ arcsin κ)   or   g ≥ σ₊(κ) = cos(½ arcsin κ)
```

for `g = subspaceGap P Q`, with `σ₋ < √2/2 ≤ σ₊`; the printed conclusion is the
low branch. Two static bounds exclude the high branch only partially:

* the `sin Θ` theorem between `A` on `P` and `A + H` on `Qᗮ`, separation `δ/2`,
  gives `g ≤ κ`;
* routing through `Q₀ = E_A([β − γ, α + γ])`, which **contains** `P` — because
  `spec(A) ⊆ [β − γ, α + γ] ∪ exterior(β − δ + γ, α + δ − γ)` and
  `spec(A₀) ⊆ [β − δ/2, α + δ/2]` cannot meet that exterior when `γ < δ/2` —
  separation `δ − γ`, gives `g ≤ γ/(δ − γ)`.

`κ < σ₊(κ)` iff `κ < √3/2`, and `γ/(δ − γ) < √2/2` iff `γ < (2 − √2)δ/2`. So the
static route proves the printed conclusion for `γ < (√3/4)δ ≈ 0.433 δ` and the
printed hypothesis is `γ < δ/2`. The shortfall is genuine.

### The connectedness step: port the bounded proof's topology

**Plan revised 2026-09-05 (human review).**  An earlier version of this section
proposed a clopen argument with the variable roots `σ₋(κ_s)`.  That is more
complicated than necessary.  The bounded proof
`theorem8_2_perturbationHalfGap_complex` already has the right bootstrap, at the
*constant* threshold `√2/2`; what has to be replaced is its bounded Riesz
continuity, not its topology.

Write `γ = ‖H‖`, `l = β − γ`, `r = α + γ`, `d = δ − 2γ > 0`, and orient the path
as the bounded proof does, so that the fixed printed gap at `Q` lives at the
start:

```text
B₀ = A + H,   B_t = B₀ − tH,   B₁ = A
R_t = specRange (B_t) (centralBand l r d)
```

The band is not a second moving interval:
`centralBand l r d = Ioo (l − d/2) (r + d/2) = Ioo (β − δ/2, α + δ/2)`, which is
exactly the extra interval Theorem 8.2 prints.

**(a) One narrow spectral-stability lemma.**  The unbounded analogue of
`realSpectrum_add_subset_of_gap`: for `t ∈ [0,1]`,
`spectrum B_t ⊆ Icc l r ∪ gapExterior l r d`.  This is bounded-perturbation
stability for an unbounded self-adjoint operator, from the existing unbounded
resolvent and inverse-norm machinery plus a Neumann step — **not** a general
continuation framework.  This is the one place real theorem work is expected.

**(a) is done, 2026-09-05.**  `GapResolvent.lean` now has
`notMem_spectrum_addBounded_of_spectrum_gap` — a gap of half-width `s` around `c`
gives a bounded inverse `R` of `c - A` with `‖R‖ ≤ s⁻¹`, and
`c - (A + K) = (1 - K R)(c - A)` on `dom A` has an invertible first factor when
`‖K‖ < s` — and its set form `spectrum_addBounded_subset_of_gap`.

**(b) `R_t` from `specRange`.**  Take the band set to be the **closed interval**
`Icc l r`, not `centralBand l r d`.  With `R_t = specRange B_t (Icc l r)`:

* the band side is immediate: `mem_resolventSet_specRestrict_of_gap` gives
  `realSpectrum (specRestrict B_t (Icc l r)) ⊆ Icc l r`, because every `lam`
  outside keeps a positive distance from the set;
* the complement side needs one step, and the tool for it is
  `specProjection_eq_zero_of_subset_resolventSet`: the two open gaps
  `(l - d, l) ∪ (r, r + d)` lie in the resolvent set of `B_t` by (a), so their
  spectral projection vanishes, hence
  `specRange B_t ((Icc l r)ᶜ) = specRange B_t (gapExterior l r d)` and the same
  resolvent lemma gives `realSpectrum ⊆ gapExterior l r d`, which is closed.
  `specProjection_add_compl_apply` and `specProjection_apply_specProjection` are
  the pieces that combine the two sets; there is **no** general
  `specProjection (S ∪ T)` additivity lemma, so this is where the assembly work
  is.

That pair is exactly `FormBoundedSylvesterGap.intervalExterior` with `β = l`,
`α = r` and gap `d`, which is what the `sin Θ` and `sin 2Θ` endpoints consume.
The endpoint inclusions `R₀ ≤ Q` and `P ≤ R₁` come from the same vanishing
argument applied to `Qᗮ` and to `P`.

**(c) is done, 2026-09-05.**  `SpectralTheory/UnboundedBandLipschitz.lean` has
`bandSubspace`, `directedGap_bandSubspace_le` and `subspaceGap_bandSubspace_le`:
`d · ‖P_{band A} − P_{band B}‖ ≤ ‖K‖` when `B = A + K`, from the unbounded
`sin Θ` theorem in each orientation with
`formBoundedSylvesterGap_band_exterior` supplying the separation.  No contour, no
continuation API.  `abs_directedGap_sub_directedGap_le` is the 1-Lipschitz
comparison that turns it into continuity of the tracked quantity.

**(d) is done, 2026-09-05.**
`Section8/Theorem82UnboundedPath.lean` carries the bootstrap.  At a fixed `t` the
`sin 2Θ` estimate is instantiated at `A := B t`, `Hop := tH`, `P := R t`, which
keeps the *printed* gap `δ` at `Q` because `B t + tH = A + H`; that gives
`δ ‖sin 2Θ (Q, R t)‖ ≤ 2tγ`, and under `f t ≤ √2/2` the double-angle comparison
turns it into `f t < √2/2`.  `f 0 = 0`, `f` is continuous by the Lipschitz
estimate, and `intermediate_value_Icc` closes it; `P ≤ R₁` transports `f 1` to
`directedGap P Q`.

`theorem8_2_perturbationHalfGap_unbounded_complex` is the directed conclusion and
`theorem8_2_perturbationHalfGap_maximalAngle_lt_unbounded_complex` the printed
`Θ < π/4`, over the **whole** printed range `‖H‖ < δ/2`.

**Every hypothesis is printed.**  The ambient placement of `A + H` that the proof
needs is derived from the two block placements by the unbounded
`realSpectrum_subset_union_of_reduces`
(`SpectralTheory/ReducingSpectrumUnion.lean`), whose proof is the direct sum of
the two block resolvents; the separation is the same two placements read as an
interval/exterior gap.

**The real port is done, 2026-09-06.**
`theorem8_2_perturbationHalfGap_unbounded_real` and
`theorem8_2_residualHalfGap_unbounded_real`, with their printed `Θ < π/4`
siblings, run the complex theorems on complexified data and read the conclusion
back.  `SpectralTheory/Complexification/ReducingRestrictionDescent.lean` carries
the transports: the block of a complexified partial map on a complexified
reducing subspace **is** the complexification of the real block, so the printed
spectral placements survive; the directed gap and the residual norm survive
because `complexify` is isometric; separability survives because the
complexification is homeomorphic to a product.

**The residual branch is done too, 2026-09-05.**
`theorem8_2_residualHalfGap_unbounded_complex` and its printed `Θ < π/4` sibling
carry `‖R‖ < δ/2` and do **not** acquire `‖H‖ < δ/2`, which was the acceptance
test.  The proof is the printed reduction: Krein's completion
(`exists_selfAdjoint_completion_eq_norm_restriction`) replaces `H` by a
self-adjoint `H'` with the same first column and `‖H'‖ = ‖R‖`, and
`A' := A + (H − H')` leaves `A' + H' = A + H` and `A'|P = A|P`.

Two supporting facts were needed and are in
`SpectralTheory/ReducingSpectrumUnion.lean`:
`invariantSubspace_orthogonal_of_isSelfAdjoint` and
`reducesSubspace_of_isSelfAdjoint_of_invariant` — the unbounded counterpart of
`reduces_orthogonalComplement`.  The complement's invariance is not assumed; it
follows from symmetry, because the projection preserves the domain and therefore
`U.starProjection '' dom A` is dense in `U`.

What remains on this row: the **real** port.

No variable root, no clopen family indexed by `κ_t`, no Riesz projector.  This
closes the **full** printed range `‖H‖ < δ/2`, not the `(√2/4)δ` sub-range the
static bound reaches.

### What is proved now

`Section8/Theorem82Unbounded.lean` holds:

* `norm_sinTwoAngleOperator_le_of_perturbedGap_unbounded_complex` — the unbounded
  `sin 2Θ` estimate read at the **operator norm**. That instantiation is possible
  only because the operator norm is the first Ky Fan norm and therefore a member
  of the source norm class, which is the inhabitation result above.
* `norm_sinTwoAngleOperator_eq_norm_block` — `‖cfc (sin 2·) Θ‖ = ‖2 P_{P⊥} P_Q P_P‖`.
  Both are the norm of the directed double-angle sine, which is symmetric in the
  pair because the *doubled* sines have the same complete approximation-number
  sequence even though the undoubled ones do not.
* `theorem8_2_branch_maximalAngle_lt_unbounded_complex` and
  `theorem8_2_branch_maximalAngle_lt_of_small_perturbation_unbounded_complex` —
  the acute conclusion from the closed branch, the second one straight from the
  printed `‖H‖ < δ/2`.

`Section8/Theorem82UnboundedBranchBound.lean` then discharges the closed branch
from the printed hypotheses alone on a sub-range of the printed one:

* `directedGap_le_of_reducingGap_unbounded_complex` — the unbounded `sin Θ`
  theorem at the operator norm, directed form: `δ · directedGap P Q ≤ ‖H‖` from
  the separation between the unperturbed block on `P` and the perturbed block on
  `Qᗮ`. At Theorem 8.2's hypotheses that separation is `δ/2`.
* `theorem8_2_branch_maximalAngle_lt_unbounded_smallPerturbation_complex` —
  `Θ < π/4` with **no** closed-branch hypothesis, under Theorem 8.2's printed
  hypotheses plus (3.5) and `2‖H‖ ≤ (√2/2)δ`.

`CrossedDefectsEquivalent.symm` was added for it: (3.5) is symmetric in the pair,
so a consumer may state it in whichever orientation its conclusion is written.

What remains is the rest of the printed range, `(√2/4)δ < ‖H‖ < δ/2`, which is
the connectedness argument above. The residual branch, and the real siblings,
come after it.

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

## 3c. The source norm class is inhabited (resolved, 2026-09-05)

The hostile review asked whether `NormalizedUnitaryInvariantNorm` is really as
broad as Davis--Kahan's Section 1 class, since it extends
`KyFanDominantIdealFamily`, which carries a completeness requirement.

Checking that turned up something sharper, and worse: **the repository had never
constructed a single term of the type.** Every occurrence was a universally
quantified hypothesis. A `∀ N : C, …` statement over an empty `C` is vacuous, so
every source-exact façade could have been true for the wrong reason.

To be precise about what was missing: the layer beneath,
`KyFanDominantIdealFamily`, *was* already inhabited, by
`KyFanDominantIdealFamily.kyFan`. What had no witness was the one extra field of
the normalized class, `gauge_rankOne_eq_one`.

`kyFanNormalizedUnitaryInvariantNorm k hk` now exhibits the `k`-th Ky Fan norm as
a member, with `nonempty_normalizedUnitaryInvariantNorm_complex` and its real
sibling as the corollaries that matter. Those are exactly the norms Davis and
Kahan's own Fan-dominance argument quantifies over, so the class contains the
ones the paper actually uses.

What remains open, and should be recorded rather than argued away: the class
requires its ideal to be **complete**, and I have not shown that every norm in
the printed class supplies that. So the Lean quantifier may still be narrower
than the printed one. Two honest resolutions, in order of preference:

1. show completeness is automatic for a normalized unitarily invariant norm in
   the source's sense (it is for every classical example -- Ky Fan, Schatten,
   Hilbert--Schmidt, trace class), and document the theorem; or
2. weaken the structure, requiring completeness only where a proof needs it.

Until one of those lands, a façade over this class is *not* known to be
exhaustive, and the final claim should say so.

## 3d. Section 4's `J` (resolved with a distinction, 2026-09-05)

The review asked for the chosen defect isometry `J` to be hidden inside the
Section 4 façades. Doing that uniformly would be wrong, and the two cases have to
be separated:

* **Proposition 4.2's `J` was genuinely proof data** -- the wrapper accepted it
  and never used it, as the underscore said. It is now the *proposition*
  `CrossedDefectsEquivalent U V`, which is the condition Section 4 actually
  inherits.
* **Propositions 4.1, 4.3 and Corollary 4.1's `J` is not proof data.** It names
  the direct rotation the conclusion is *about*. Quantifying over every `J`, as
  those theorems do, is the stronger reading and is what a caller holding a
  particular rotation wants. Replacing it by an existential would weaken the
  theorem, and in the non-acute case there is no canonical choice to substitute.

So the canonical statements keep their `J`, and
`proposition4_3_compact_nonacute_sourceExact_ofCrossedDefects_{complex,real}`
serve the caller who has only the source's hypothesis: they take
`CrossedDefectsEquivalent` and name a direct rotation for which the minimality
holds. The same wrapper should be added for Proposition 4.1 and Corollary 4.1.

## 4. Finish unbounded Theorem 8.2

The source theorem types are written and the estimate halves are proved; see
§10.4. What is left is exactly one thing, and §10.4 states it precisely: the
closed quarter branch `‖P_P − P_Q‖ ≤ √2/2` under the printed hypotheses.

* **Theorem 8.1 does not supply it.** 8.1 inherits the `tan 2θ` theorem's
  off-diagonality `H₀ = H₁ = 0`; 8.2 inherits the `sin 2θ` theorem's hypotheses,
  which have none. The earlier claim to the contrary is corrected in §10.4.
* The static bounds reach `‖H‖ < (√3/4)δ`, not the printed `‖H‖ < δ/2`.
* The connectedness argument that closes it needs the parametrized unbounded band
  subspace `Q_s = E_{A + sH}(B_s)` and an unbounded ambient `sin Θ` theorem, and
  nothing from the general Riesz/continuation roadmap.

Protect the residual alternative from accidental extra perturbation hypotheses.

## 3b. Theorem 3.1's real forward invariant — **done, 2026-09-05**

The complex forward theorem states the classification on the source's angle
operator (`genericAngleBlock`); the real one was on `genericCosineBlock`, which
is the wrong invariant. It is now
`theorem3_1_spectralMultiplicity_classification_sourceAngle_real`, canonical on
the `complete-invariant.real` clause.

**The Mathlib blocker recorded here was not real.** The note said
`StarOrderedRing (E →L[ℝ] E)` does not exist, so the complex proof could not be
transcribed and complexification was required. In fact Mathlib proves
`ContinuousLinearMap.instStarOrderedRingRCLike` for a general `RCLike` field and
declines to *register* it, because it takes the continuous functional calculus
as an argument and Mathlib has that only at `𝕜 = ℂ`;
`ForTauCeti.Analysis.InnerProductSpace.RealContinuousFunctionalCalculus` supplies
the real calculus and demonstrates the instance, and
`Section3Classification.lean` already imported it. Installing it with
`attribute [local instance]` — which is how the rest of the repository uses it —
lets the complex proofs transcribe line for line.

What was actually built:

* `genericCosineBlock_nonneg_real`, `genericCosineBlock_le_one_real`,
  `spectrum_genericCosineBlock_subset_Icc_real` — the complex proofs with the
  local instance;
* `genericAngleBlockReal` — a separate definition only because
  `Algebra ℝ (E →L[𝕜] E)` is unavailable for a bare `RCLike 𝕜`;
* `RealSpectralRestriction.sameSpectralMultiplicity_cfc_iff_real` — the complex
  transport with `OperatorUnitaryEquiv.cfc_ofReal`,
  `cfc_cfc_eq_self_of_leftInverse_real` and the real classification pair
  substituted;
* `theorem3_1_spectralMultiplicity_classification_sourceAngle_real`.

The two derived `[SeparableSpace (genericLeftHalf …)]` instances were also
removed from the complex statement: separability of a subspace of a separable
space is a consequence, and both statements now carry only the source's own
ambient separability.

## 4b. Reviewed working order and validation discipline (human, 2026-09-05)

Do these in this order, and do not spend time on `8.1 → 8.2`, variable-root
algebra, generic Riesz-continuation infrastructure, or complexifying the real
Theorem 3.1 invariant:

1. real Theorem 3.1 by the direct local-instance route — **done**;
2. the spectral-stability lemma for the path — **done**;
3. `R_t := specRange B_t (Icc l r)` with its band and exterior spectra — **done**;
4. the two-direction `sin Θ` Lipschitz estimate for `R_s`, `R_t` — **done**;
5. the bounded proof's constant-`√2/2` IVT bootstrap; its endpoint inclusions are
   done (`le_of_band_exterior_spectra`), so what is left is the moving family,
   the continuity of `t ↦ directedGap R_t Q`, and the connectedness step;
6. the complex perturbation source theorem — **done**;
7. the residual branch, by the self-adjoint-completion reduction the bounded
   proof already uses — **done**; its public type carries `‖R‖ < δ/2` and does
   not acquire `‖H‖ < δ/2`;
8. the real port, through the existing partial-map complexification layer —
   **done**; separate exact real and complex endpoints, not an `RCLike`
   generalization;
9. resolve the UIN completeness question below — **answered, §4c**;
10. hand back a source-exact snapshot for hostile review — **the certification
    pass ran green on 2026-09-06**; see §XVI.6 for what it found and fixed.

**Validation discipline for this stretch.**  Do not run the whole
inventory/census/statement-map/name-drift/pin suite after ordinary commits.  Use
a targeted build of the touched modules, the relevant `#check`s, the specific
hostile regression involved, and statement pins only when a public theorem
changed.  Save the expensive aggregate and certification run for semantic
closure.

## 4c. The UIN completeness question: answered and implemented

**It was never an open mathematical question, and it is now closed in the code.**

The measurement, 2026-09-05:

* Completeness is **not** derivable from the properties Davis and Kahan print.  A
  symmetric gauge determines an ideal that need not be complete for its gauge;
  `SymmetricNormingFunction`, which is DK's own class, carries no completeness
  field.  So option (1) is unavailable.
* Completeness **is** genuinely needed by part of the analytic layer: about ten
  theorem families take `[N.toOperatorIdealFamily.IsComplete]` explicitly,
  because their limiting arguments need the ideal to be a Banach space.
* Completeness is **not** used by the Fan-dominance bridge, nor — as the
  implementation then proved — by any theorem the source-facing façades route
  through.

**Option (2), implemented 2026-09-06.**  `KyFanDominantIdealFamily` is split:

```text
FanDominantIdealFamily     -- symmetric ideal family + Fan dominance
KyFanDominantIdealFamily   -- extends it, and adds `isComplete`
```

`NormalizedUnitaryInvariantNorm` — the source-facing norm quantifier — now
extends the **completeness-free** base, so a source theorem quantified over it no
longer implicitly restricts the norm class.  `Mem`, `gauge` and the small bridges
moved to the base; a `CoeOut` from the complete family to the base is what let
the roughly 150 existing binder sites keep passing the stronger structure without
being touched.

The refactor is the empirical answer to the question the analysis left open:
**every theorem the source façades depend on went through unchanged**, so none of
them used completeness.  The families that do need it keep it.

## 5. Fresh hostile review of all designated results

Review source statements against compiler-expanded theorem types.

Fix only actual source mismatches.

## 6. One final certification pass — run 2026-09-06

The full (non-`--fast`) suite ran and is green except three failures that are not
Davis--Kahan and not new: the two TauCeti readiness/roadmap gates, which are about
unplaced `ForTauCeti.Probability.*` modules, and the `per-declaration-expose`
ratchet, which `dev/policy/ratchet.yaml` says in as many words is above its
maximum today and must not be made green by raising it.

It found two real things that `--fast` cannot see, and both are fixed:

* **Statement-pin drift** on `theorem3_1_spectralMultiplicity_classification_sourceAngle_complex`,
  from removing its two derived separability instances, plus the new real
  source-angle statement being unpinned.  Both re-pinned with the reason.
* **A tamper mutation that had stopped biting.**
  `ambient-realization-replaced-by-non-ambient` keyed on a `"primary"` the
  Theorem 3.1 converse stopped using when it moved to the printed multiplicity
  hypothesis.  Retargeted.  This is the failure mode the tamper suite exists to
  catch in itself, and only a full run makes it visible.

**DK-8.2-thm's canonical evidence was promoted to unbounded scope** in the same
pass: `theorem8_2_branch_maximalAngle_lt_unbounded_source_complex` and its real
sibling state the printed disjunction — either `‖H‖ < δ/2` or `‖R‖ < δ/2` — at
the paper's inherited unbounded ambient scope, and the bounded siblings are
retained as specializations.  The separability posture for the row moves from
`mixed` to `separable`, with both witnesses classified as load-bearing: the
unbounded `sin 2Θ` estimate the bootstrap consumes is built on the spectral
measure of the Cayley transform, which is stated for separable spaces.

**DK-8.1-thm is the row that is still not at its source scope.**  Its unbounded
angle conclusion exists (§10.3), but branch existence and parts (i)--(iii) remain
bounded, so its canonical evidence is unchanged.

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

## XVII.1 Scoreboard, 2026-09-06

Measured, not asserted.  Every line below is checkable from
`dev/davis-kahan-1970-formalization-result-inventory.json` and a build.

| Condition | Status |
| --- | --- |
| every designated result has canonical Lean evidence at its actual source scope | **29 of 29** as of 2026-09-06; DK-8.1-thm's canonical evidence was promoted to the unbounded witnesses once they existed in both scalar fields |
| real/complex coverage for every result | met |
| canonical façades expose the paper's separability scope | met, and every separable canonical witness is classified in `ambient_scope_policy.separability` |
| finite vs infinite-dimensional scope matches each printed result | met — including Theorem 8.1 (ii) and (iii), which the source prints *in finite dimensions* (§10.3) |
| bounded vs unbounded scope matches each printed result | met — Theorem 8.1's branch existence, both halves of its printed *iff*, and part (i) are canonical at unbounded scope in complex and real scalar scope; (ii) and (iii) stay finite because the source prints them so |
| every UIN-quantified theorem uses the literal source abstraction at its boundary | met, and as of §4c that abstraction no longer carries completeness |
| no canonical theorem asks for a hypothesis absent from the paper | met |
| source objects, gaps, ordered angles, residuals, constants, conclusions agree | met, re-checked by the tamper suite and the 95 statement pins |
| **Theorems 8.1 and 8.2 cover their inherited unbounded scope** | met — both, in complex and real scalar scope, 8.1 including both halves of the printed *iff* |
| the exact/stronger distinction stays visible in the census | met |
| a fresh source-first review finds no material statement mismatch | run; it found two defects, both fixed (§XVI.6) |
| the final certification pass succeeds | run 2026-09-06, green apart from three failures that are not Davis--Kahan |

**Every line above is now met.**  The last mathematical gap — the converse half of
Theorem 8.1's printed characterization at unbounded scope — closed on 2026-09-06
(§10.3.3), the real unbounded endpoints followed by complexification, and
DK-8.1-thm's canonical evidence was promoted to the unbounded witnesses in both
scalar fields.  `scripts/certify_davis_kahan_1970.py` reports `status: PASS` with
29/29 terminal, 1412/1412 registered declaration signatures, and zero production
build warnings.

Two things a reader should not over-read in that.  First, the certificate proves
compilation, declaration resolution and pin stability; it does not prove that a
Lean statement says what the paper says, which is what the hostile semantic review
is for and why the canonical-evidence digest gates it.  Second, promotion is a
judgement the record exposes rather than hides: DK-8.1-thm and DK-8.2-thm remain
classified as accepted **nonlocal source interpretations**, because Theorem 8.1
states no hypotheses of its own and Theorem 8.2 states its own only as an
addition.  What the unbounded lift changed is that the scope half of that
question is now moot — the delivered evidence is exact under the alternative
literal reading and a proper generalization under the accepted bounded one, so no
reviewer decision about what "the hypotheses of the tan 2θ theorem" imports
changes what the repository has.

The remaining call is a human one: whether to make the §XVIII claim.

---

# XVIII. Final public claim

When the conditions above are satisfied, the repository may claim;

> **The designated Davis–Kahan 1970 results have been formally resolved in Lean at the mathematical scope of their original statements, including the applicable real and complex, separable-Hilbert-space, unbounded-operator, and arbitrary normalized unitary-invariant norm scope. Stronger generalizations are recorded separately and are not used to conceal missing source-exact evidence.**

If the designated inventory contains a source or transcription assertion that is formally refuted rather than proved, state that separately and do not collapse it into the phrase “all theorems proved.”

Supplemental sharpness, examples, asymptotics, extensions, and stronger APIs may be described separately.

The formalization claim is about **the Davis–Kahan results themselves**.

That is the finish line.
