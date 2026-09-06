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

**(d) The bounded proof's constant-threshold bootstrap — remaining.**  At a fixed
`t`, instantiate the unbounded `sin 2Θ` estimate at `A := B_t`, `Hop := tH`,
`P := R_t`, `Q := Q` — legitimate because `B_t + tH = B₀`, so the `δ` in the gap
stays the *fixed printed gap at `Q`* rather than shrinking with `t`.  That gives
`δ ‖sin 2Θ (R_t, Q)‖ ≤ 2tγ`.  Under `f t ≤ √2/2`,
`sqrt_two_mul_directedGap_le_norm_sinTwoAngleOperator` gives
`√2 · f t ≤ ‖sin 2Θ (Q, R_t)‖`, hence `√2 · f t · δ ≤ 2tγ ≤ 2γ < δ` and
`f t < √2/2`.  With `f 0 = 0` and `f` continuous, the bounded theorem's own IVT
step gives `f t < √2/2` for every `t`, and `P ≤ R₁` turns `f 1` into
`directedGap P Q`.

Two identifications are what is left, and both are the same argument:

* `R₀ ≤ Q`.  `Q` is only *assumed* to reduce `B₀` with spectrum in `[β, α]` on
  `Q` and in the exterior on `Qᗮ`; that determines it, so `Q` is the spectral
  range `specRange hB₀ (Icc β α)`, and `[β, α] ⊆ [l, r]` gives the inclusion.
  The step that needs API is the uniqueness: a vector of `R₀` splits along `Q`,
  its `Qᗮ` part has spectrum in the exterior and therefore no spectral mass on
  `[l, r]`, so it vanishes.  What that needs is the commutation of
  `specProjection` with `P_Q` for a reducing `Q`.
* `P ≤ R₁`, the same argument at `t = 1` with the printed containment
  `spec(A₀) ⊆ [β − δ/2, α + δ/2] ⊆ [l, r]`.

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
5. the bounded proof's constant-`√2/2` IVT bootstrap, whose remaining
   prerequisite is the commutation of `specProjection` with the projection onto a
   reducing subspace, which gives both endpoint inclusions;
6. the complex perturbation source theorem;
7. the residual branch, by the self-adjoint-completion reduction the bounded
   proof already uses.  Its public type must carry `‖R‖ < δ/2` and must **not**
   acquire `‖H‖ < δ/2`; that is the acceptance test;
8. the real port, through the existing partial-map complexification layer, as
   `Theorem81Real.lean` does.  Separate exact real and complex endpoints are
   enough — this is not another `RCLike` project;
9. resolve the UIN completeness question below;
10. hand back a source-exact snapshot for hostile review.

**Validation discipline for this stretch.**  Do not run the whole
inventory/census/statement-map/name-drift/pin suite after ordinary commits.  Use
a targeted build of the touched modules, the relevant `#check`s, the specific
hostile regression involved, and statement pins only when a public theorem
changed.  Save the expensive aggregate and certification run for semantic
closure.

## 4c. The UIN completeness question needs a binary answer

`NormalizedUnitaryInvariantNorm` extends `KyFanDominantIdealFamily`, which
carries `isComplete`.  The source's own list of unitary-invariant-norm properties
does not state completeness.  Before source-exact signoff, do exactly one of:

1. prove that completeness follows from the norm class Davis--Kahan quantify
   over; or
2. remove completeness from the source-facing abstraction and keep it on the
   stronger internal `KyFanDominantIdealFamily` layer.

Do not leave it labelled an open question, and do not stop the Section 8 proof to
redesign the norm layer unless it actually blocks it.

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
