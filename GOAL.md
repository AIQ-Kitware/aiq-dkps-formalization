# Davis–Kahan 1970 — Final 100% Completion and Hostile-Review Closure Plan

**Baseline:** repository state at `2613ae44` or later, incorporating the completed repairs through the latest hostile-review cycle.

## Objective

Finish the Davis–Kahan 1970 formalization under the strongest defensible source-correspondence standard:

1. Every designated Davis–Kahan result has a **source-exact Lean façade** whose expanded type matches the paper's mathematical statement and standing scope.
2. Stronger theorems remain available and are explicitly registered as **generalizations**, rather than being substituted for the paper theorem.
3. The census can answer both questions independently:

   * **Did the project formalize exactly what Davis–Kahan state?**
   * **What stronger forms have also been proved?**
4. No semantic claim rests only on declaration names, comments, conventions, or reviewer interpretation when a compiled correspondence theorem can be supplied.
5. The final hostile review should be able to begin with the original paper, ignore the repository's previous conclusions, and reconstruct the same 29/29 result.

A temporary loss of `29/29` while the remaining source-exact surfaces are being completed is acceptable. Do not preserve a green number by treating an unresolved scope question as a policy exception.

---

# Progress record — 2026-09-05

Kept here so a reader knows what is done without re-deriving it. Items not listed
are not started.

## Done

**§V — the regression invariants.** `Audits/HostileReviewRegressions.lean`
restates each repair and proves it by the declaration, so a drift stops the module
elaborating. It exists because statement pins follow *canonical* declarations: when
the source-exact façades became canonical, eight repaired theorems dropped out of
the pinned set and could have drifted back unnoticed. No new checker and no new
data file.

**§III.3 beyond Section 2 — done.** Corollary 4.1, Proposition 4.3, Theorem 5.2,
Theorem 6.3 and Theorem 8.2's two retained double-angle bounds all have façades
over both scalar fields. Theorem 6.3 reuses Section 2's directed-tangent façades;
the Section 4 and Theorem 5.2 results were already proved from
`KyFanDominantIdealFamily`, so a source norm reaches them by its own projection.

**§III — the literal source norm class.** `NormalizedUnitaryInvariantNorm`
(`DavisKahan/OperatorIdeal/NormalizedUnitaryInvariantNorm.lean`) is the Lean type
for Section 1's object. It extends `KyFanDominantIdealFamily`, so the ideal domain
(`∞` off the ideal, preserving the source's "the norm may not exist here"), the
norm axioms, contraction compatibility and Fan dominance come with it; the one
thing not already available, the rank-one normalization, is its only new field.
Nonnegativity, definiteness, equation (1.9) unitary invariance, contraction
compatibility and adjoint invariance are **derived theorems**, not assumed, so a
caller supplies irredundant data. §3.2's bridge is
`normalizedUnitaryInvariant_of_symmetricNorming`, plus a `_mul` form carrying the
source constant 2. No Calkin theory was introduced, per §3.2.

**§III.3 + §IV — source-exact façades for Section 2.** Twelve of the thirteen
clauses. Each states its clause at the printed scope: separable ambient Hilbert
space, literal UIN class, unbounded self-adjoint ambient operator. Only the
*ambient* space carries separability (§4.2). §4.3's split into `ℝ` and `ℂ` is done
for `S2-sin-theta`.

**§X — the exact/stronger distinction, in the existing schema.** The façades are
canonical; the arbitrary-Hilbert `SymmetricNormingFunction` theorems and the
`RCLike` theorem are registered as `generalization`. Two gates were updated to
follow the reversed policy **with their discipline kept**: separability posture is
still derived from compiler types and every separable witness must still be
classified; the scalar-generic tripwire still requires the generic witness to stay
registered and audited.

**A supporting generalization.** Fan dominance is now heterogeneous — it was
stated for one pair of spaces, which blocked every clause comparing operators
between different spaces. Both existing constructors satisfy the stronger field
unchanged.

## Known gaps, precisely

* **`S2-tan-two-theta` directed real** has no façade. Its two sides live over
  different scalar fields: the tangent corner exists only on the complexification
  while the residual is real, and `NormalizedUnitaryInvariantNorm 𝕜` is indexed by
  one field where `SymmetricNormingFunction` is not. Recorded in
  `TanTwoThetaUnboundedExactReal.lean` with the two routes out.
* **`S2-tan-two-theta` directed complex** has a façade but keeps the older
  primary. That clause's contract requires the *primary itself* to compose its
  five-step transport chain; a thin façade delegates. Loosening that check would
  defeat its purpose. Closing it means building the façade from the
  block-representative theorem with the transport composed inside.
* **`DK-8.1-thm`** has no UIN-quantified clause to give a façade to: its parts (i)
  and (ii) are compression and eigenvalue repulsion, and part (iii) is the
  explicitly finite-dimensional symmetric-gauge statement. §IV separability for its
  clauses is not done.
* **§XI, §XII, §XIII, §XV** not started.
* **§6.2 is DONE**, and it turned out much smaller than the plan assumed. The plan
  expected a new unbounded Lax--Milgram: closedness, coercivity, closed range, an
  adjoint/kernel argument, then the bounded inverse. None of that was needed.
  Coercivity of `J (A − c)` against an *isometry* already forces the norm lower
  bound `δ‖x‖ ≤ ‖A x − c x‖` by Cauchy--Schwarz, the triangle inequality spreads
  it over `(c − δ, c + δ)` with constant `δ − |lam − c|`, each point is then a
  resolvent point by the existing `mem_resolventSet_of_lower_bound`, and the
  existing gap resolvent gives the two-sided bounded inverse of norm `≤ δ⁻¹`.
  `TauCeti.LinearPMap.mem_resolventSet_of_coercive_comp` and
  `TauCeti.DavisKahan.twoSidedShiftedInverseBound_of_coercive_comp` are the two
  theorems, both axiom-clean. `J` need only preserve norms, so a reflection
  qualifies.
* **§6.3 is half done.** The repulsion half is lifted:
  `notMem_spectrum_addBounded_of_offDiagonal_form_gap` is the source Section 8
  repulsion statement for an unbounded self-adjoint `A` with a bounded
  off-diagonal `H`, stated in exactly the shape
  `twoSidedShiftedInverseBound_of_spectrum_gap` consumes. Its ingredient
  `reflected_centered_form_lower_pmap` is the coercivity of the reflected
  centered *partial* map; the bounded hypothesis "`U` is invariant" becomes "`U`
  reduces `A`", which is what keeps `P x` and `P^⊥ x` in the domain. The
  off-diagonal/skew half is reused verbatim, because `H` is still bounded.
* **`isQuarterAcute_of_orderedFormGap` is the one genuinely open piece of §VI, and
  the obstruction is now identified precisely.** It is not the coercive inverse —
  that is §6.2 and it is done. The bounded proof forms `B = J(A−c)` and
  `C = K(A+H−c)`, both `≥ δ`, uses the exact Lyapunov identity
  `C W + W* C = 2B` with `W = KJ` unitary, and then conjugates `W` by `C^{1/2}`
  to turn strict accretivity into a strict spectral half-plane bound, which for a
  *unitary* `W` gives `W + W* > 0`, i.e. `‖P_U − P_V‖² < 1/2`.

  With `A` unbounded, `C` is unbounded and `C^{1/2}` is not available as a
  bounded operator. Two facts survive and should be the starting point:

  1. `W = KJ` preserves `dom(A)`, because `J` reduces `A` and `K` reduces `A+H`,
     and `dom(A+H) = dom(A)`;
  2. the Lyapunov identity is *equivalent*, in form terms, to the single
     inequality `re ⟪W x, C x⟫ ≥ δ‖x‖²` on `dom(A)`, and substituting `x = C⁻¹ y`
     (legitimate: `C⁻¹` is bounded by §6.2 and maps `H` onto `dom(A)`) makes it a
     statement about bounded operators only:
     `re ⟪W C⁻¹ y, y⟫ ≥ δ ‖C⁻¹ y‖²`.

  Two candidate routes:

  * **(a) form-relative boundedness.** `B = W* C − J H` with `H` bounded, so
     `Z = C^{-1/2} B C^{-1/2}` is bounded exactly when `W* C` is `C`-form
     bounded. Establish that and the bounded argument transports.
  * **(b) approximate eigenvectors.** `W` is unitary, so a spectral point has an
     approximate eigenvector; the naive estimate fails because `‖C xₙ‖` is
     unbounded. Choosing the approximating sequence inside a spectral subspace of
     `A` on which `C` is bounded would repair it.

  Neither is a formalization detail; this is real operator theory and should be
  scoped as its own task.
* **§VII–§VIII (Theorem 8.2 unbounded)** not started, and §VII remains the largest
  single piece. Note that §7.1's core already exists:
  `exists_norm_le_two_sided_shifted_inverse_of_spectrum_gap` is the unbounded
  self-adjoint resolvent with the `1/dist` bound. What is missing is §7.3, the
  contour/Riesz layer, and §7.4.

---

# I. Final source-correspondence policy

Adopt the following rule globally:

> **Canonical source evidence must state the paper theorem at the paper's actual scope. Stronger mathematics belongs immediately underneath or beside it and is registered separately as a generalization.**

This resolves the previous policy questions.

For Hilbert-space results, a source-exact façade must therefore carry the source-wide separability assumption.

For the paper's real/complex scalar scope, the exact evidence should expose the real and complex instances as the source witnesses. Arbitrary `RCLike` theorems are valuable stronger variants and should remain available.

For unitary-invariant norms, the exact source façade must quantify over a Lean abstraction that actually represents the source's normalized unitary-invariant norm class.

Do not weaken existing general theorems to achieve this. Add thin source façades around stronger results.

## Required census distinction

Every result/clause should have two independently machine-readable evidence classes:

```text
source-exact evidence
    exact paper field
    exact paper separability/dimension scope
    exact source hypotheses
    exact source mathematical object
    exact source norm abstraction
    exact constant and conclusion

stronger evidence
    broader scalar class
    nonseparable Hilbert spaces
    weaker hypotheses / broader gap abstractions
    more general norm model
    stronger conclusion
    other genuine mathematical extension
```

The census must never use a stronger theorem as a replacement for missing source-exact evidence.

---

# II. Correct the Section 8 scope decision

## Decision

**Theorem 8.1 and Theorem 8.2 must be formalized for unbounded self-adjoint ambient \(A\), at the scope inherited from the double-angle theorems.**

The original paper establishes this scope strongly enough that the current bounded-only interpretation should be retired.

The source gives several mutually reinforcing signals:

* The opening setup says that the results and proofs apply to unbounded self-adjoint \(A\) under the stated domain condition.
* Immediately after the four Section 2 theorems, Davis–Kahan say the theorems cover unbounded self-adjoint operators, that the relevant spectral blocks may otherwise be unbounded, and that the technical modifications needed for this generality are concentrated in Theorem 5.2 and the Appendix to Section 6.
* Section 7 explicitly says the `tan 2θ` proof shown for bounded operators and compact \(S_0\) extends to the general case by the same method used for `tan θ`.
* Theorem 8.1 says to assume the hypotheses of the `tan 2θ` theorem, and Theorem 8.2 says to add hypotheses to the `sin 2θ` theorem. Neither introduces a bounded-\(A\) reset.
* Theorem 8.1 explicitly marks only some subordinate statements as finite-dimensional, showing that the authors were distinguishing scope locally when they intended to.

Therefore delete the bounded-only policy exception once the unbounded endpoints land. `DK-S8-UNBOUNDED` is a real completion obligation.

---

# III. Introduce the literal source unitary-invariant norm abstraction

The paper quantifies over arbitrary normalized unitary-invariant norms, and explicitly invokes Ky Fan dominance to reduce inequalities for all such norms to the finite Ky Fan norms.

The development currently has excellent stronger/analytic abstractions such as:

```text
SymmetricNormingFunction
KyFanDominantIdealFamily
```

The recent equivalence work shows that the relevant estimates reduce to the same Ky Fan inequalities. Preserve all of that.

What is still required for maximal source exactness is an actual Lean representation of the norm object Davis–Kahan quantify over.

## 3.1 Define the source mathematical abstraction

Add a general mathematical type with a non-provenance name such as:

```text
NormalizedUnitaryInvariantNorm
```

or, if the partial-domain nature requires it,

```text
UnitaryInvariantNormFamily
```

Do not call the mathematical type `Paper...` or `Source...`.

It must model the source's actual Section 1 notion, including:

* the ideal/domain on which the norm exists;
* norm nonnegativity and definiteness;
* homogeneity;
* triangle inequality;
* invariance under unitary multiplication on either side;
* normalized rank-one value;
* contraction compatibility / ideal monotonicity.

Do **not** model it as a finite real-valued function on every bounded operator. The paper explicitly allows cases where the norm in a result does not exist; the formal type must preserve that partial/ideal character.

## 3.2 Prove the Fan-dominance bridge

Prove a compiled bridge from the literal UIN object into the existing Ky-Fan machinery:

```text
NormalizedUnitaryInvariantNorm
        ↓
finite Ky Fan dominance
        ↓
KyFanDominantIdealFamily / existing estimate machinery
```

Reuse the newly proved equivalence between the symmetric-norm and Ky-Fan estimate schemes.

The goal is to formalize the source's own reduction, not rebuild the analytic proofs.

A formal Calkin-algebra example is **not required** for completion. Do not expand scope into Calkin theory merely to exhibit a norm outside `SymmetricNormingFunction`.

## 3.3 Add exact UIN façades to every relevant source result

Any canonical Davis–Kahan witness whose printed conclusion says “for every unitary-invariant norm” must ultimately quantify over the literal UIN abstraction.

The existing `SymmetricNormingFunction` and `KyFanDominantIdealFamily` theorems become registered stronger/analytic variants.

This applies at minimum to the four Section 2 families and all later results whose statements use the same UIN quantifier.

## Acceptance criterion

A compiler-expanded canonical theorem should visibly quantify over the literal UIN abstraction. The proof body may immediately reduce it through Fan dominance.

---

# IV. Add exact separable source façades

The paper globally works in a separable real or complex Hilbert space.

Adopt exact separability for canonical source evidence even where the underlying theorem proves a stronger arbitrary-Hilbert result.

## 4.1 Add thin wrappers only at the source boundary

Do not add separability assumptions to reusable analytic infrastructure.

For each source-facing Hilbert-space result:

```text
general theorem
    arbitrary Hilbert space
        ↓
thin DavisKahan1970 façade
    separable Hilbert space
```

The general theorem remains the preferred reusable theorem outside the source package.

## 4.2 Do not expose derived component assumptions

If the source only assumes that the ambient Hilbert space is separable, do not ask the source-facing caller separately for separability of every reducing subspace or coordinate space.

Derive those instances internally from:

* subspace separability;
* isometric embeddings/equivalences;
* the already proved Hilbert-dimension correspondences.

In particular, the exact Theorem 3.1 surface should derive whatever component-space separability it needs from the source data rather than exposing additional assumptions absent from the paper.

## 4.3 Scalar policy

Canonical source evidence should cover:

```text
𝕜 = ℝ
𝕜 = ℂ
```

because those are the source scalar fields.

Existing or new arbitrary

```lean
{𝕜 : Type*} [RCLike 𝕜]
```

results should be retained and registered as stronger scalar-generic variants.

Do not discard the `RCLike` work.

---

# V. Preserve and lock the source-correspondence repairs already completed

Before starting new foundations, add a short regression checklist covering the defects found during hostile review.

These are currently considered repaired and must not regress:

* directed `sin 2Θ₀` uses the source residual rather than the full perturbation;
* directed `sin 2Θ₀` is on the trial-side ordered angle;
* Theorem 8.2 uses the same correct trial-side orientation;
* ambient `sin 2Θ` puts the spectral gap on the source's \(\Lambda_0,\Lambda_1\) blocks of \(A+H\);
* Theorem 3.1's forward invariant is stated on the paper's angle-operator multiplicity invariant rather than only `genericCosineBlock`;
* Corollary 3.1's classification is stated on the actual angle sequence/eigenvalue data;
* Theorem 3.1 derives \(J_0\) from multiplicity data instead of requiring it as caller-supplied proof data;
* Theorem 3.1's ambient-dimension clause is a proposition rather than a chosen equivalence;
* condition `(3.5)` is connected by theorem to the paper's Hilbert-dimension statement at separable scope;
* `tan Θ` source semantics use the paper's definedness/vacuity convention rather than importing `(3.5)` backward into Section 2;
* tangent endpoints disclose pole exclusion/definedness in their conclusions;
* Theorem 5.1 carries Banach scope and an actual compatible norm;
* Theorem 5.2 real and complex source endpoints use the printed ordered gap;
* Lemma 5.1 canonical evidence is an actual proof, not a capability facade;
* source-facing theorem signatures contain no CFC or other proof-capability typeclasses.

Add focused invariants for these when cheap. Do not run a broad comparator on every edit.

---

# VI. Complete unbounded Theorem 8.1

This is the smaller of the two remaining analytic foundations.

## 6.1 Target the exact source theorem first

Write the target theorem signature before implementing infrastructure.

It should inherit the already source-exact **unbounded** `tan 2θ` hypotheses and state all of Theorem 8.1's printed conclusions.

Do not invent additional boundedness hypotheses just because the current proof infrastructure is bounded.

Respect the source's existing vacuity/definedness handling where a norm must exist.

The exact theorem must include the source's scope distinctions:

* the principal `Θ ≤ π/4` characterization at general scope;
* existence of the appropriate reducing projector \(Q\);
* operator inequality (i) at its actual scope;
* the finite-dimensional statement in (ii), together with the source's stated natural infinite-dimensional extension if that is represented as a source atom;
* the explicitly finite-dimensional symmetric-gauge statement (iii).

Do not generalize the finite-dimensional clauses in the canonical source theorem merely because a stronger version can be proved.

## 6.2 Prove the minimal unbounded coercive inverse theorem

The current obstruction is the bounded `CoerciveUnit` route used by:

```text
isQuarterAcute_of_orderedFormGap
```

The missing reusable theorem is essentially:

```text
A self-adjoint, possibly unbounded
J a bounded reflection
ordered/coercive form gap for J(A - c)
        ↓
J(A - c) has a bounded inverse on its natural domain
with the required inverse norm/coercivity estimate
```

Implement this in `ForTauCeti`, at the `LinearPMap`/closed-operator layer, rather than inside the Section 8 source module.

Keep the result as narrow as the actual consumer permits. Do not build a broad unbounded-operator library unless the proof requires it.

A likely route is:

1. closedness/dense domain of the shifted self-adjoint operator;
2. coercivity gives injectivity and closed range;
3. the adjoint/kernel argument gives dense or full range;
4. construct the bounded inverse;
5. obtain the \(1/\delta\)-type norm estimate.

## 6.3 Lift the two bounded-specific Section 8.1 ingredients

Generalize:

```text
realSpectrum_add_offDiagonal_subset_exterior_of_form_gap
isQuarterAcute_of_orderedFormGap
```

to the unbounded `LinearPMap` setting using:

```text
specRange
selfAdjointSpectralSubspace
reducesSubspace_specRange
SpectralFormBounds
addBounded_isSelfAdjoint
```

Reuse existing bounded theorems as specializations.

## 6.4 Prove the unbounded source theorem

Once `IsQuarterAcute` follows from the ordered unbounded form gap, lift the existing Theorem 8.1 argument.

Provide exact real and complex source façades with separability and the literal UIN norm abstraction where relevant.

Then retain:

* bounded Theorem 8.1 as a specialization;
* arbitrary-Hilbert form as a stronger variant when available;
* `RCLike` form as a stronger variant when available.

At this point remove the bounded-only Section 8 interpretation from canonical certification.

---

# VII. Build the minimal unbounded resolvent/Riesz layer needed by Theorem 8.2

This is the largest remaining piece.

Do not attempt a general-purpose holomorphic functional calculus unless forced by the proof. Build the smallest reusable self-adjoint resolvent/contour layer that supports the existing continuation argument.

## 7.1 Unbounded self-adjoint resolvent

For self-adjoint `LinearPMap A`, provide a bounded resolvent object for \(z\notin\sigma(A)\):

```text
(A - z)⁻¹ : H →L[ℂ] H
```

with:

* left/right inverse statements on the appropriate domain;
* self-adjoint spectral-theorem grounding;
* the standard bound

  $$
  \|(A-z)^{-1}\| \le 1/\operatorname{dist}(z,\sigma(A));
  $$
* compatibility with `addBounded`;
* the second resolvent identity for bounded perturbations.

Prefer complex-first implementation followed by the repository's established real-complexification transport.

## 7.2 Gap stability under bounded perturbation

For

```text
A(t) = A + tH
```

with self-adjoint unbounded \(A\) and bounded self-adjoint \(H\):

* prove self-adjointness on the common domain;
* prove the source-required spectral gap remains open under the half-gap norm condition;
* expose the distance-to-spectrum estimate needed by the contour.

## 7.3 Unbounded Riesz/spectral projection

Lift the bounded `CircleRieszProjection` / continuation machinery only as far as needed to prove norm continuity of the isolated spectral branch.

Required properties:

* contour integral of the unbounded resolvent produces a bounded projection;
* it agrees with the self-adjoint spectral projection / `specRange` for the isolated interval;
* it varies continuously, preferably Lipschitz with the same estimate used by the bounded continuation proof;
* the projection is compatible with the bounded perturbation path.

If there is a shorter proof directly for `specRange` using the spectral theorem and resolvent identity, prefer that over constructing a broad new functional calculus.

## 7.4 Lift the continuation stack

Generalize the bounded objects currently used by Theorem 8.2:

```text
SpectralSeparatingContour
SpectralContinuationWitness
selectedBranchProjectionLipschitzConstant
operatorPath
```

to the unbounded-self-adjoint-plus-bounded-perturbation setting.

The bounded implementation should become a specialization of the more general infrastructure where practical.

---

# VIII. Complete unbounded Theorem 8.2

## 8.1 Perturbation-norm branch

Prove the exact source theorem for:

$$
\|H\| < \delta/2
$$

with unbounded self-adjoint \(A\) and bounded self-adjoint \(H\), using the lifted continuation path

$$
A(\sigma)=A+H-\sigma H.
$$

The theorem must conclude both:

* the source `sin 2Θ` inequality already inherited from the source theorem;
* the acute conclusion \(\Theta < \pi/4\).

Do not substitute a nearby angle representation.

## 8.2 Residual-norm branch

Prove the source alternative

$$
\|R\| < \delta/2
$$

using the source's Krein reduction/choice of perturbation exactly as the bounded proof does, now over the unbounded ambient operator.

Do not assume \(\|H\|<\delta/2\) in the public residual theorem.

## 8.3 Unequal-dimension extension

The source immediately states an unequal-dimension extension of the `sin 2θ` theorem.

Ensure its registered scope is consistent with the same unbounded interpretation rather than leaving the extension bounded merely because the existing proof happens to be bounded.

## 8.4 Exact real/complex façades

End with source-exact:

```text
real + separable + literal UIN
complex + separable + literal UIN
```

as canonical evidence.

Register the bounded and arbitrary-Hilbert/RCLike forms as stronger or specialized variants as appropriate.

After this phase `DK-S8-UNBOUNDED` is closed and the old Section 8 scope-policy exception is deleted.

---

# IX. Finish and preserve the stronger theorem layer

Once every source result has an exact façade, make the stronger mathematics easy to discover.

For each source result, register every meaningful existing generalization, including where applicable:

* arbitrary Hilbert space instead of separable;
* arbitrary `RCLike` instead of fixed real/complex;
* broader form-gap abstractions;
* arbitrary reducing subspaces;
* source theorem as a specialization of more general residual data;
* `KyFanDominantIdealFamily`;
* `SymmetricNormingFunction`;
* stronger domain/general operator forms.

Do not manufacture artificial “stronger” theorems solely to populate a table. Register genuine mathematical extensions.

## Finish the remaining scalar-generic Section 2 API

If `SectionTwo.sinTwoTheta` or another short `RCLike` endpoint is still awaiting scalar-transport work, finish it after the source-exact layer is complete.

The final generic directed theorem must reach:

```text
Angle.directedSinTwoAngleOperator
```

and not stop at:

```text
sinTwoThetaIdealBlock
```

or another proof representative.

The exact source census does **not** depend on the short generic name once real and complex source façades are complete. The generic theorem is a stronger API result.

---

# X. Make exactness and generalization first-class census data

The current evidence schema should be extended so a reader does not have to infer whether a declaration is the exact paper theorem or a stronger replacement.

A useful conceptual shape is:

```json
{
  "source_exact_evidence": [
    {
      "scalar": "real",
      "declaration": "...",
      "expanded_type_checked": true
    },
    {
      "scalar": "complex",
      "declaration": "...",
      "expanded_type_checked": true
    }
  ],
  "stronger_variants": [
    {
      "declaration": "...",
      "generalization_axes": [
        "drops_separability",
        "rclike_scalar_generic",
        "broader_gap"
      ],
      "source_specialization": "compiled theorem or wrapper showing the source case"
    }
  ]
}
```

Reuse the current `canonical_evidence` / `supporting_evidence` schema if it can express this just as clearly; avoid gratuitous schema churn.

## Machine-check the distinction

For source-exact evidence, verify from the compiler-expanded type:

* correct fixed scalar field;
* separability where the paper assumes it;
* source UIN norm abstraction;
* arbitrary versus finite dimension exactly as printed;
* bounded/unbounded operator scope exactly as printed;
* correct trial/exact/reducing subspace roles;
* correct angle orientation;
* correct residual versus perturbation RHS;
* correct operator carrying the spectral gap;
* exact source constants;
* no implementation-capability classes;
* no caller-provided correspondence witness that the source derives internally.

For stronger evidence, require a concrete specialization/correspondence route back to the exact source façade whenever practical.

A declaration should never be labeled “stronger” merely because its name or prose says so.

---

# XI. Re-audit the denominator and supplemental source assertions

Keep the **29-result denominator** stable unless the original-source audit proves it is wrong.

However, the final public claim should survive the objection:

> “You proved 29 named results but omitted other mathematical claims Davis–Kahan explicitly establish.”

Before final sign-off, re-audit all source atoms against the original PDF.

Pay particular attention to the Section 2 assertions currently treated as sharpness commentary:

* optimality of the constants;
* two-dimensional equality examples;
* direct sums attaining equality simultaneously for all UIN norms;
* first-order asymptotic equivalence as the perturbation tends to zero.

For maximal certainty, formalize these as **supplemental proved source assertions** even if they remain outside the named 29-result denominator.

Apply the same rule to any other nontrivial Davis–Kahan-established assertion currently excluded only because it appears in prose rather than a named theorem environment.

Do not turn proof steps, definitions, externally cited facts, historical remarks, or open questions into artificial result obligations.

The eventual claim should distinguish:

```text
29/29 designated result obligations resolved exactly

plus

all additional nontrivial DK-established source assertions
tracked in the fidelity inventory are either formally proved/refuted
or explicitly classified outside the formalization claim for a principled reason
```

---

# XII. Perform a fresh source-first hostile review before the heavy gates

Once implementation is complete, stop modifying the certificate and conduct a fresh semantic review.

The reviewer should start from the **original PDF**, not from `canonical_evidence`.

For each of the 29 result rows:

1. transcribe the mathematical statement independently;
2. identify inherited source-wide and section-wide assumptions;
3. inspect the compiler-expanded canonical theorem type;
4. compare every quantified object;
5. compare scalar field;
6. compare separability and dimension scope;
7. compare bounded/unbounded scope and domains;
8. compare all gap assumptions and which operator carries them;
9. compare trial/exact/reducing roles;
10. compare ordered directed angles;
11. compare residual versus perturbation quantities;
12. compare norm abstraction and ideal membership;
13. compare constants;
14. compare conclusions;
15. verify every source-to-internal representation step has a compiled theorem.

Do the same for every explicit result-scope extension attached to those rows.

Do not mark a row exact because a source-shaped wrapper exists. Inspect its expanded type.

---

# XIII. Add targeted semantic tamper tests

The certificate should deliberately fail under mutations corresponding to every serious bug previously found.

At minimum tamper-test:

```text
R ↔ H on the RHS
P/Q or trial/exact order swap
gap moved from Λ-blocks to A-blocks
directed angle replaced by proof block
source UIN replaced by SymmetricNormingFunction only
separability removed from exact façade
unbounded A replaced by bounded-only witness
real/complex source witness replaced by fixed complex only
extra CFC capability binder
extra crossed-defect hypothesis in Section 2 tan Θ
finite-dimensional specialization substituted for arbitrary-dimensional theorem
Theorem 3.1 Θ multiplicity replaced by generic cos² block without correspondence
zero-multiplicity restriction reintroduced in Corollary 3.1
caller-supplied J₀ or tangent correspondence reintroduced
```

These should be narrow tests. There is no need to run the entire heavy suite for each mutation.

**Done, 2026-09-05.** `dev/policy/tamper-mutations.yaml` holds fourteen mutations
and `aiq-lean tamper run` is a slow gate in the suite; all fourteen are rejected
by the gate named against them, and the run refuses to start on a dirty tree,
restores each file from the bytes it read, and fails if the tree is left
modified. Two design points are worth keeping:

* Every gate is first run on the *unmutated* tree. A gate that already fails
  would otherwise "detect" every mutation put to it, which is the exact failure
  mode this section exists to prevent.
* Every mutation here is a **registration** defect -- a row pointing at a
  statement that is not the one the paper prints -- because that is the class all
  three external reviews actually found. Lean-source mutations are deliberately
  absent: the type probes read compiled `olean`s, so a Lean mutation only bites
  after a rebuild, and a suite costing a full build per mutation would never be
  run. The Lean side is covered instead by `Audits/HostileReviewRegressions.lean`
  (section V), which restates each repaired invariant and proves it *by* the
  registered declaration, so a statement that drifts stops compiling.

The list below maps onto the shipped mutations; where a line names a Lean-level
swap, the entry retargets the row at the weaker statement that models it.

---

# XIV. Validation policy during implementation

Until all semantic work above is finished, use only targeted validation:

* compile the touched theorem/module;
* compile its direct source-facing wrapper;
* run `DavisKahan.Audits.All` when shared source infrastructure changes;
* run `Challenge` when generic scalar/operator infrastructure changes;
* run the affected inventory/census static checker;
* run the specific statement pins or tamper tests relevant to the edit.

**Do not run comparator-scale or full clean certification repeatedly.**

Do not delete `.lake`.

Do not run `certify_davis_kahan_1970.py --clean` during ordinary implementation.

A green full certificate is not evidence that a source-semantic change is correct.

---

# XV. One final expensive certification pass

Only after the fresh hostile semantic review reports no findings:

1. freeze the source specification and source-atom inventory;
2. ensure the tree is clean;
3. run the full incremental build;
4. run all source audit aggregates;
5. run `Challenge`;
6. run declaration-name drift;
7. run all statement pins;
8. run source census;
9. run result inventory;
10. run statement map;
11. run semantic-review coherence;
12. run the complete tamper suite;
13. run comparator/canonical-evidence checks;
14. run the final clean certification **once**, if a clean-root build is part of the release certificate;
15. verify zero production warnings;
16. verify every compiler-probed canonical declaration resolves;
17. verify the source files did not change during certification.

No semantic fix should be made after this pass without invalidating the final certificate and rerunning the relevant final checks.

---

# XVI. Final publication/census presentation

The generated result report should make the distinction between source exactness and stronger mathematics obvious.

For each result, show something equivalent to:

```text
DK-… — PASS

Printed scope:
  separable real or complex Hilbert space
  [other source hypotheses]
  arbitrary normalized unitary-invariant norm

Exact Lean evidence:
  ℝ: ...
  ℂ: ...

Stronger variants:
  arbitrary RCLike: ...
  nonseparable Hilbert space: ...
  broader gap form: ...
  SymmetricNormingFunction: ...
  KyFanDominantIdealFamily: ...
```

Do not describe the stronger variants as necessary to establish source coverage.

## Final top-level claim

Once every step above is complete, the defensible claim is:

> **All 29 designated Davis–Kahan 1970 result obligations have been formally resolved at their printed source scope over separable real and complex Hilbert spaces, including the paper's unbounded-operator scope and arbitrary normalized unitary-invariant norms. The false transcribed assertion is formally refuted rather than counted as proved. The census separately records stronger generalizations proved by the development.**

If the supplemental source-assertion pass is also complete, add:

> **The source-fidelity census also tracks the paper's additional established sharpness, equality, asymptotic, and scope assertions outside the 29 named result obligations.**

Do not say merely “29/29 proved,” because the formally refuted source assertion must remain distinguishable.

---

# Definition of 100% complete

Do not stop because:

```text
lake build is green
29/29 is green
the certificate passes
all declarations resolve
```

Stop only when all of the following are simultaneously true:

* exact real and complex source façades exist for every result clause;
* source separability is present on canonical Hilbert-space evidence;
* the literal source UIN norm abstraction is present on every relevant canonical theorem;
* all stronger variants are preserved and separately identified;
* Theorems 8.1 and 8.2 are complete at unbounded source scope;
* every known source/internal representation difference has a compiled correspondence theorem;
* the source census distinguishes exact evidence from stronger evidence;
* supplemental nontrivial DK assertions have been audited and, where appropriate, formalized;
* a fresh PDF-first hostile review has zero open findings;
* semantic tamper tests reject every major historical regression class;
* the final expensive certification pass is green;
* production build warnings are zero;
* the repository tree is clean and the final source/certificate hashes are frozen.

That is the finish line.

