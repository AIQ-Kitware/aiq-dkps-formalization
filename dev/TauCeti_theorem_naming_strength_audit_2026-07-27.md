# Tau Ceti theorem naming and strength audit

**Snapshot reviewed:** `aiq-dkps-formalization` at merge snapshot `4285a6e`  
**Purpose:** Identify public declarations whose names suggest a stronger or more canonical mathematical result than the implementation currently provides, and recommend Mathlib-style names that remain honest as the library grows.

## Executive conclusion

Most of the current named results are mathematically honest. In particular, finite-dimensional Courant-Fischer, Eckart-Young, singular-value, Schatten-norm, and Moore-Penrose declarations are not false or illegitimate merely because stronger infinite-dimensional versions also exist. Their finite-dimensional scope is visible in their types or namespaces.

There are, however, five declaration families whose current names materially overstate or obscure what is implemented:

1. `ContinuousLinearMap.polarIsometry`
2. `TauCeti.polarUnitary`
3. `FiniteDimensional.inverseOnRange`
4. `UnitaryInvariantIdealFamily`
5. the `*_infinite` tan-two-theta declarations whose active graph data remains finite-dimensional

The first four should be renamed or redesigned before becoming canonical Tau Ceti APIs. The fifth should be renamed before upstreaming its module. None of these issues blocks the initial approximation-number PR.

---

## Naming policy

Use the unsuffixed classical name only when the declaration implements the canonical object or theorem at the generality a mathematically informed reader would normally infer.

Restricted but genuine versions are acceptable when the restriction is visible through one or more of:

- a namespace such as `FiniteDimensional`;
- explicit typeclass hypotheses;
- an `_of_...` suffix naming a material assumption;
- a suffix such as `_finiteDimensional`, `_compact`, `_of_isUnit`, or `_of_injective`;
- module documentation that clearly describes the scope.

Avoid total definitions with junk behavior outside the theorem's valid regime under names that imply a canonical mathematical object.

For theorem names, prefer conclusion-first Mathlib-style names:

```text
<conclusion>_of_<material hypotheses>
```

Use `exists_...` for noncanonical existential choices. Reserve a bare noun such as `polarUnitary` for a genuinely canonical object.

---

## Severity levels

- **Block upstreaming:** The name or definition would create a misleading canonical API.
- **Rename before its PR:** The result is correct, but the name advertises more generality than the theorem has.
- **Compatibility cleanup:** The name obscures a stronger bundled assumption or duplicates another declaration.
- **Optional polish:** The current name is honest; a rename would only improve Mathlib style.

---

# Findings

## 1. `ContinuousLinearMap.polarIsometry`

**Location**

```text
ForTauCeti/Analysis/InnerProductSpace/Polar/Isometry.lean
```

**Current declaration**

```lean
noncomputable def ContinuousLinearMap.polarIsometry
    (M : E →L[ℂ] F) : E →L[ℂ] F :=
  M ∘L Ring.inverse M.modulus
```

The implementation is the correct polar isometric factor only when `M.modulus` is a unit. Outside that case, `Ring.inverse M.modulus` is zero, so the definition is zero. Consequently, the total definition is not generally an isometry and is not the partial isometry from the general polar decomposition.

### Does the name overclaim?

**Yes. This is the clearest overclaim in the current API.**

A reader encountering `M.polarIsometry` would reasonably infer that the returned map is the canonical polar isometry or partial isometry associated with every bounded operator. The implementation instead encodes a conditional construction using a totalized inverse.

### Recommended redesign

Best option:

```lean
noncomputable def polarIsometricFactorOfIsUnitModulus
    (M : E →L[ℂ] F) (hM : IsUnit M.modulus) : E →L[ℂ] F
```

The hypothesis can be accepted by the definition rather than carried by every theorem.

Reasonable shorter alternatives:

```lean
polarIsometryOfIsUnitModulus
polarFactorOfIsUnitModulus
polarIsometricFactorOfBoundedBelow
```

The current implementation can remain as a private helper:

```lean
private noncomputable def polarIsometryAux
```

### Recommended theorem renames

| Current name | Recommended name |
|---|---|
| `polarIsometry_apply` | `polarIsometricFactorOfIsUnitModulus_apply` |
| `polarIsometry_comp_modulus` | `polarIsometricFactor_comp_modulus` |
| `polarIsometry_modulus_apply` | `polarIsometricFactor_modulus_apply` |
| `norm_polarIsometry_apply` | `norm_polarIsometricFactor_apply` |
| `isometry_polarIsometry` | `isometry_polarIsometricFactor` |
| `polarIsometry_injective` | `polarIsometricFactor_injective` |
| `norm_sub_polarIsometry_apply_eq` | `norm_sub_polarIsometricFactor_apply_eq` |
| `norm_sub_polarIsometry_apply_le_norm_modulus_sub_one` | `norm_sub_polarIsometricFactor_apply_le_norm_modulus_sub_one` |

The exact prefix should follow the final definition name.

### Upstream decision

**Block this module's upstreaming until renamed or redesigned.**

This does not block the approximation-number PR.

---

## 2. `TauCeti.polarUnitary`

**Location**

```text
ForTauCeti/Analysis/InnerProductSpace/Polar/Decomposition.lean
```

**Current declaration**

```lean
noncomputable def polarUnitary (A : E →ₗ[𝕜] E) : E ≃ₗᵢ[𝕜] E
```

For singular square operators, the canonical polar factor is a partial isometry. A unitary extension can be chosen in finite dimensions by extending the isometry on the orthogonal complement of the kernel, but this extension is generally not unique. The implementation chooses one through `LinearIsometry.extend`.

### Does the name overclaim?

**Yes, primarily by implying canonicity.**

The construction is mathematically valid as a selected unitary factor satisfying `A = U |A|`. The problem is that `polarUnitary A` sounds like *the* polar unitary associated canonically with `A`, whereas singular operators admit many unitary extensions.

### Recommended rename

Preferred:

```lean
noncomputable def choosePolarUnitary
    (A : E →ₗ[𝕜] E) : E ≃ₗᵢ[𝕜] E
```

More explicitly existential:

```lean
theorem exists_polarUnitary (A : E →ₗ[𝕜] E) :
    ∃ U : E ≃ₗᵢ[𝕜] E, A = (U : E →ₗ[𝕜] E) ∘ₗ abs A
```

A private choice can then be made from that theorem if downstream construction needs a concrete witness.

Other acceptable names:

```lean
chosenPolarUnitary
kernelCompletedPolarUnitary
polarUnitaryExtension
```

### Recommended theorem renames

| Current name | Recommended name |
|---|---|
| `polarUnitary_apply_abs_apply` | `choosePolarUnitary_apply_abs_apply` |
| `polar_decomposition_unitary` | `polar_decomposition_choose_unitary` or `exists_polar_decomposition_unitary` |

The existing invertible-case declaration is substantially better named:

```lean
polarUnitaryEquiv (hA : IsUnit A)
```

It is uniquely tied to the invertible polar factor and may remain, though a name such as `polarUnitaryEquivOfIsUnit` would better expose the material hypothesis.

### Upstream decision

**Rename before the polar-decomposition PR.**

The underlying mathematics need not be discarded.

### Resolution 2026-07-28 — RESOLVED

`polarUnitary → choosePolarUnitary`, `polarUnitary_apply_abs_apply → choosePolarUnitary_apply_abs_apply`, `polar_decomposition_unitary → polar_decomposition_choosePolarUnitary`; 40 references across 8 files. The section docstring now states outright that the kernel completion is a choice, and points at `polarUnitaryEquiv` for the invertible case where the factor is genuinely unique.

`exists_polar_decomposition_unitary` was added as the audit recommends, and is the statement downstream users should prefer when they need only *some* unitary factor.

One recommendation deliberately not taken: `polarUnitaryEquiv` is **not** renamed to `polarUnitaryEquivOfIsUnit`. The audit floats this without requiring it. The declaration takes `(hA : IsUnit A)` as an explicit argument, so the material hypothesis is already visible in the signature; `_of_` suffixes on *definitions* rather than theorems are not the Mathlib convention; and that factor really is canonical, so the bare name is honest.

---

## 3. `FiniteDimensional.inverseOnRange`

**Location**

```text
ForTauCeti/Analysis/InnerProductSpace/MoorePenroseInverse.lean
```

**Current declaration**

```lean
noncomputable def inverseOnRange
    (A : E →ₗ[𝕜] F) (_hA : Function.Injective A) : F →ₗ[𝕜] E :=
  moorePenroseInverse A
```

This is a total map on all of `F`. Its behavior outside `range A` is the Moore-Penrose extension, not an inverse whose domain is literally `range A`.

### Does the name overclaim?

**Moderately.**

It does not overstate a theorem's strength, but it misdescribes the domain and mathematical object. A true inverse on the range would normally have source type `LinearMap.range A` or be a left inverse packaged with its law.

### Recommended approach

Delete the alias and use the honest canonical name:

```lean
moorePenroseInverse
```

For the injective left-inverse theorem, retain:

```lean
moorePenroseInverse_comp_eq_id_of_injective
```

If an actual inverse on the range is needed, define:

```lean
noncomputable def rangeInverseOfInjective
    (A : E →ₗ[𝕜] F) (hA : Function.Injective A) :
    LinearMap.range A →ₗ[𝕜] E
```

or package a linear equivalence:

```lean
noncomputable def linearEquivRangeOfInjective
    (A : E →ₗ[𝕜] F) (hA : Function.Injective A) :
    E ≃ₗ[𝕜] LinearMap.range A
```

### Recommended removals and renames

| Current declaration | Recommendation |
|---|---|
| `inverseOnRange` | Delete alias, or replace with a map whose domain is `range A` |
| `inverseOnRange_eq_moorePenroseInverse` | Delete with alias |
| `inverseOnRange_comp_eq_id` | Use `moorePenroseInverse_comp_eq_id_of_injective` |
| `moorePenroseInverse_eq_inverseOnRange` | Delete compatibility theorem |

### Upstream decision

**Remove or redesign before the Moore-Penrose module is upstreamed.**

The definition `moorePenroseInverse` itself is honest: it is explicitly finite-dimensional and computes the standard pseudoinverse.

### Resolution 2026-07-28 — RESOLVED by deletion

All four declarations are gone: `inverseOnRange`, `inverseOnRange_eq_moorePenroseInverse`, `inverseOnRange_comp_eq_id`, `moorePenroseInverse_eq_inverseOnRange`. The surviving content is `moorePenroseInverse_comp_eq_id_of_injective`, which the audit already identified as the honest form of the left-inverse law.

Two corrections to the section as written:

- The suggested replacement `linearEquivRangeOfInjective : E ≃ₗ[𝕜] LinearMap.range A` did **not** need to be built — it is Mathlib's `LinearEquiv.ofInjective`. So the redesign was a pure deletion.
- The three consumers in `DavisKahan/FiniteDimensional/Residual/AngleEmbeddings.lean` were not renamed but **deleted**, because they were weaker than the audit realised: since `inverseOnRange A hA` was a definitional alias for `moorePenroseInverse A`, and `tanThetaEmbedding` is *defined* by `moorePenroseInverse`, all three "compatibility" theorems were restatements of `rfl` and carried no content. The one genuinely useful fact buried in them — the translation of transversality into injectivity — is now stated on its own as `cosThetaMagnitude_injective_of_isTransverse`.

The closing caveat this section used to carry, that the API did not yet have all four Penrose equations, is also out of date: they were proved (with uniqueness) on 2026-07-28, so `moorePenroseInverse` is now certified to *be* the Moore-Penrose inverse rather than merely some generalized inverse.

---

## 4. `UnitaryInvariantIdealFamily`

**Location**

```text
DavisKahan/OperatorIdeal/ApproximationNumbers/ScalarGeneric.lean
```

**Current declaration**

```lean
abbrev UnitaryInvariantIdealFamily :=
  KyFanDominantIdealFamily
```

`KyFanDominantIdealFamily` bundles a rectangular symmetric ideal family together with a full finite-Ky-Fan majorization principle:

```lean
majorization_mem_and_gauge_le
```

The alias gives this stronger structure the broad name `UnitaryInvariantIdealFamily`.

### Does the name overclaim?

**Yes, by hiding a material extra assumption.**

Not every type one might reasonably call a unitarily invariant ideal family should definitionally include a supplied proof of the full dominance principle. The current abbreviation makes downstream theorem signatures look more general than they are.

### Recommended design

Keep the stronger structure name:

```lean
KyFanDominantIdealFamily
```

and use it directly wherever the cutoff argument genuinely needs Ky Fan dominance.

Longer-term preferred separation:

```lean
structure UnitaryInvariantIdealFamily ...
class HasKyFanDominance (N : UnitaryInvariantIdealFamily ...) : Prop ...
```

Then theorems can expose the requirement:

```lean
theorem ... (N : UnitaryInvariantIdealFamily ...) [HasKyFanDominance N] ...
```

If the broad base object is not yet ready, do not introduce the broad alias. Continue using `KyFanDominantIdealFamily`.

### Upstream decision

**Delete the alias before upstreaming the ideal-family API.**

Source-facing Davis-Kahan wrappers may use prose such as "unitarily invariant ideal family satisfying Ky Fan dominance," but the Lean type should preserve the stronger name.

### Resolution 2026-07-28 — RESOLVED by deletion

The alias is gone and all 94 references across 30 files now name `KyFanDominantIdealFamily` directly, so every downstream signature states the Ky Fan dominance it actually requires.

This was safe to do as one sweep because it was a **spelling change, not a migration**: `structure KyFanDominantIdealFamily (𝕜 : Type u) [RCLike 𝕜]` and the alias took identical arguments, and all 92 call sites used the single form `UnitaryInvariantIdealFamily (𝕜 := X)`. No statement, proof body, or elaboration changed.

The audit's licence for prose was taken up rather than ignored: three docstrings that described the hypothesis as an "arbitrary/every real unitarily invariant ideal family" now say **Ky-Fan-dominant** unitarily invariant ideal family, which is what the theorems require.

The longer-term separation the section also floats — a genuinely broad `UnitaryInvariantIdealFamily` structure plus a `HasKyFanDominance` mixin — was deliberately **not** attempted. The section itself says "If the broad base object is not yet ready, do not introduce the broad alias"; deleting is what it asks for now, and building the base structure is a design lane rather than a naming fix.

---

## 5. `*_infinite` tan-two-theta names

**Location**

```text
DavisKahan/DoubleAngle/TanTwoThetaKyFanInfinite.lean
```

**Current declarations include**

```lean
kyFan_doubleAngleTangent_offDiagonal_le_infinite
kyFan_tanTwoTheta0_offDiagonal_le_infinite
tanTwoTheta0_offDiagonal_mem_and_gauge_le_infinite
```

The ambient Hilbert space may be infinite-dimensional, but the active invariant graph or carrier used by the theorem remains finite-dimensional.

### Does the name overclaim?

**Yes, unless "infinite" is read only as an ambient-space qualifier.**

Most readers will interpret an `_infinite` suffix and a module title promising "infinite dimensions" as the unrestricted infinite-dimensional theorem. The current theorem is better described as an ambient-space lifting of a finite-dimensional active configuration.

### Recommended renames

Preferred suffixes:

```lean
_of_finiteDimensional_invariantGraph
_of_finiteDimensional_carrier
_in_infiniteDimensional_ambient
```

Concrete proposals:

| Current name | Recommended name |
|---|---|
| `kyFan_doubleAngleTangent_offDiagonal_le_infinite` | `kyFan_doubleAngleTangent_offDiagonal_le_of_finiteDimensional_invariantGraph` |
| `kyFan_tanTwoTheta0_offDiagonal_le_infinite` | `kyFan_tanTwoTheta0_offDiagonal_le_of_finiteDimensional_invariantGraph` |
| `tanTwoTheta0_offDiagonal_mem_and_gauge_le_infinite` | `tanTwoTheta0_offDiagonal_mem_and_gauge_le_of_finiteDimensional_invariantGraph` |

If the actual finite object is named differently in the theorem signature, substitute that exact mathematical noun for `invariantGraph`.

Recommended module rename:

```text
TanTwoThetaKyFanFiniteCarrier.lean
```

or:

```text
TanTwoThetaKyFanAmbient.lean
```

### Upstream decision

**Rename before upstreaming this theorem family.**

This is a naming correction, not a demand to finish the unrestricted theorem first.

### Resolution 2026-07-28 — RESOLVED

All three declarations renamed and the module renamed to `DavisKahan/DoubleAngle/TanTwoThetaKyFanFiniteCarrier.lean` (the audit's own suggestion, and the one that matches the file's Method paragraph, which already said "Everything happens inside the finite-dimensional carrier `M := U ⊔ T '' U`").

The suffix used is `_of_finiteDimensional_invariantSubspace`, **not** the table's `_of_finiteDimensional_invariantGraph`. The audit itself says to substitute the exact mathematical noun from the signature if it differs, and it does: the hypothesis is literally `[FiniteDimensional 𝕜 U]` on the invariant **subspace** `U`. The graph of `T` is what builds the carrier, but no object named `invariantGraph` appears in the statement.

The module docstring, which previously advertised "infinite dimensions", now states the scope plainly: the ambient space may be infinite-dimensional, the active configuration may not, and this is an ambient-space lifting of the finite-dimensional theorem rather than the unrestricted one.

---

## Audit status summary (2026-07-28)

| item | status |
|---|---|
| 1. `ContinuousLinearMap.polarIsometry` | **RESOLVED 2026-07-29 by rename — `polarIsometry` → `polarIsometryOfIsUnitModulus`, whole name family (17 declarations), and the four prose cross-references.** The hypothesis is now in the name, per this document's own policy. **The severity was understated: the declaration sat in the *root* `ContinuousLinearMap` namespace**, so it claimed Mathlib's unqualified classical name for an object requiring `IsUnit |M|`, alongside `ContinuousLinearMap.polarPartial` — the general object — in that same namespace. That is *block upstreaming*, not *rename before its PR*. Not deleted, because it carries the sharp near-isometry estimate `polarPartial` does not have; deleting remains the eventual end state once that estimate is restated over `polarPartial`. **VERDICT CORRECTED 2026-07-29 — see the item-1 addendum; do not delete this module on the strength of the text below.** The three results named as blockers have zero references and are trivially rehoused; the content actually at risk is the sharp near-isometry estimate, which `polarPartial` does **not** carry. Original text follows. **PARTIAL — reconciliation proved 2026-07-28** (`polarPartial_eq_comp_ringInverse_modulus`: the two agree wherever the light one is meaningful). Retirement still open, and larger than it looks: the module also carries two `IsUnit \|M\|` criteria and `‖\|M\| - 1‖ ≤ ‖M⋆M - 1‖`, none of them polar-decomposition results, which need rehousing before anything is deleted. Original situation: — the general partial isometry now exists as `ContinuousLinearMap.polarPartial` (`ForTauCeti/Analysis/InnerProductSpace/Polar/PartialIsometry.lean`, 44 declarations), and `PolarIsometry.lean` carries a live `TODO` to prove `polarIsometry = polarPartial` under `IsUnit M.modulus` and then **retire** `polarIsometry` in favour of the general one. That supersedes the section's own recommendation: the audit proposed renaming to `polarIsometricFactorOfIsUnitModulus` and keeping the definition, but if the general object is available the honest move is deletion, not a longer name. Retiring it is the open lane; renaming it would entrench a definition that is scheduled to go. |
| 2. `TauCeti.polarUnitary` | **RESOLVED** — renamed `choosePolarUnitary`, `exists_polar_decomposition_unitary` added |
| 3. `FiniteDimensional.inverseOnRange` | **RESOLVED** — alias family deleted |
| 4. `UnitaryInvariantIdealFamily` | **RESOLVED** — alias deleted, 94 references repointed to `KyFanDominantIdealFamily` |
| 5. `*_infinite` tan-two-theta names | **RESOLVED** — renamed, module renamed to `TanTwoThetaKyFanFiniteCarrier` |

---

# Addendum: item 1 re-measured, 2026-07-29 — the recorded verdict is wrong

Item 1 is the only finding from the original audit still open, and its status-table entry
records a verdict that the tree does not support. Correcting it here rather than acting on it,
because the correction changes what the right action *is*.

**What the status table says.** That retirement is *"larger than it looks"* because the module
also carries two `IsUnit |M|` criteria and `‖|M| - 1‖ ≤ ‖M⋆M - 1‖`, *"none of them
polar-decomposition results, which need rehousing before anything is deleted"*, and that since
`polarPartial` exists, *"the honest move is deletion, not a longer name."*

**Measurement, 2026-07-29.** Both halves are off, in opposite directions.

1. **The three "blocking" results are not a blocker.** `isUnit_modulus_iff`,
   `isUnit_modulus_of_norm_adjoint_comp_self_sub_one_lt_one` and `norm_modulus_sub_one_le` are
   self-contained on `modulus` — none mentions `polarIsometry` — and each has **zero references
   anywhere in the repository**. Rehousing them is a copy, not a migration.

2. **The actual content at risk is the near-isometry estimate, which the entry does not mention.**
   `PolarIsometry.lean` proves `‖M - M.polarIsometry‖ ≤ ‖M⋆M - 1‖` (`norm_sub_polarIsometry_le`),
   sharp, over arbitrary complex Hilbert spaces. **`polarPartial` does not have this.**
   `PolarPartialIsometry.lean` contains no `norm_sub_*` bound at all. So "delete in favour of the
   general object" would delete a theorem the general object does not provide.

3. **The module reads as dead and is not.** Nothing imports
   `ForTauCeti.Analysis.InnerProductSpace.Polar.Isometry`; its only mentions outside itself are
   three lines of prose. That looks like textbook dead code — but it is a *terminal* statement,
   and `NearIsometry.lean`, which **is** consumed and is pinned by
   `comparator/pending-near-isometry.json`, carries a design note naming it *"the general theorem
   and the canonical object"* and directing readers to it for the complex case. Deleting it
   orphans a cross-reference from a comparator-pinned module and removes the general form of a
   result the real case only approximates.

**Corrected recommendation.** Deletion is not the honest move; the audit's *original* proposal was
closer. Either (a) restate the near-isometry estimate over `polarPartial` — the reconciliation
theorem `polarPartial_eq_comp_ringInverse_modulus` makes this available under `IsUnit |M|` — and
only then delete, or (b) keep the definition and rename it to expose the hypothesis, moving the
three `modulus` results to `PolarDecomposition.lean` where `modulus` is defined. Both are real
work; neither is "delete it". What is **not** acceptable is deleting the module on the strength of
the current entry, which is why this correction is filed before anyone acts on it.

**Why the entry was wrong is worth keeping.** It was written when `polarPartial` had just appeared
and the reconciliation theorem had not been proved. "The general object exists, so the special one
is redundant" is true of the *object* and false of the *theorems stated about it* — generality of a
definition does not transfer the lemmas. That failure mode is easy to repeat anywhere this
repository supersedes a bundled notion with a raw one.

---

# Addendum: re-sweep of 2026-07-29

**Why this section exists.** Everything above is a snapshot of `4285a6e`, and four of its five
findings are now resolved. Nothing had re-run the audit's policy against the tree since. The
current `ForTauCeti` surface is **237 `def`/`abbrev`/`structure` and 1085 `theorem`/`lemma`**, a
large fraction of it added after the original pass, so the resolved status table above should not
be read as "the surface is clean".

**Method.** The audit's own three defect patterns, applied mechanically and then checked by hand:
(i) bare classical names on restricted objects, (ii) total definitions with junk behaviour outside
their valid regime, (iii) names hiding a material hypothesis. Reference counts are over
`ForTauCeti/**` and `DavisKahan/**` only, excluding `vendor/` and `external/`.

**What did *not* turn up, recorded so the next sweep does not redo it.** `abs`, `sqrt`,
`moorePenroseInverse`, `spectrum`, `resolvent` and the `schattenNorm` family all looked like
candidates and all survive: each is either guarded by an explicit hypothesis (`sqrt` takes
`T.IsPositive`), restricted by a visible `[FiniteDimensional …]` instance, or genuinely canonical.
`chosenHilbertBasis`/`chosenHilbertBasisSet` are **models** of the convention, with a docstring that
says outright that nothing depends on the choice.

## 6. `TauCeti.IsBddMeasurable.bound` — arbitrary choice under a definite-article name

**Location:** `ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/Operator.lean:52`

```lean
noncomputable def bound {f : spectrum ℂ a → ℂ} (hf : IsBddMeasurable f) : ℝ :=
  hf.exists_bound.choose
```

**The defect.** `bound` is *a* bound extracted by `Classical.choose`, not *the* bound. It is neither
the supremum nor the least admissible constant, and nothing pins it down. A reader meeting
`hf.bound`, `bound_nonneg` and `norm_le_bound` will reasonably take it for the sup-norm of the
symbol, and every estimate stated in terms of it is therefore weaker than it looks.

**Severity: rename before its PR.** What makes this more than style is that **the repository has
already set the opposite convention twice, in resolving findings 2 and 4 of this very document** —
`polarUnitary` became `choosePolarUnitary`, and the Hilbert basis is `chosenHilbertBasis` with an
explicit "nothing depends on which" docstring. `bound` is the same construction under the naming the
audit rejected.

**Recommendation.** `chooseBound`, with `chooseBound_nonneg` / `norm_le_chooseBound`. If a canonical
constant is wanted later, the honest object is `⨆ x, ‖f x‖`, which is a different declaration and
should not silently inherit this name.

## 7. `TauCeti.permEV` — abbreviation that reads as the wrong noun

**Location:** `ForTauCeti/Analysis/InnerProductSpace/EigenvalueChange.lean:128` (19 references)

**The defect.** `EV` abbreviates **Euclidean vector** — the docstring says "Coordinate permutation of
a Euclidean vector". But the declaration lives in `EigenvalueChange.lean`, in a
spectral-perturbation library, where `EV` is read as *eigenvalue* by default. The name says the
opposite of what it means in the one context it appears in. Mathlib also does not use unexplained
two-letter abbreviations in declaration names.

**Severity: rename before its PR.** Mechanical, 19 call sites, no statement changes.

**Recommendation.** `permuteCoords`, or `EuclideanSpace.permute` if it is worth namespacing.

## 8. `sortedEig` — abbreviation only, and it is not the cheap rename it looks like

**Location:** `ForTauCeti/Analysis/Matrix/SpectralFunctionMeasurable.lean:70` (30 references)

`Eig` for eigenvalues. Honest, just not mathlib style. **Severity: optional polish.**
**Recommendation:** `sortedEigenvalues`.

**Correction — I attempted this rename and backed it out, and the reason is the useful part.**
Renaming the `def` alone is 30 references in four files and takes ten minutes. But `sortedEig` is
also embedded in **six theorem names** — `abs_sortedEig_sub_le_of_entry_le`,
`abs_sortedEig_le_of_entry_le`, `measure_forall_sortedEig_ge_ge`,
`measure_forall_abs_sortedEig_sub_le_ge`, `measure_forall_sampleCovariance_sortedEig_ge_ge` and the
`Matrix.`-namespaced form (all six are quoted here as the **historical** names they bore on
2026-07-27; `sortedEig` became `sortedEigenvalues` in `37df3c57`, and `sampleCovariance` became
`sampleSecondMoment` on 2026-08-05) — and one of those, `TauCeti.measure_forall_sortedEig_ge_ge`, is **pinned
by name in `comparator/pending-matrix-concentration.json`**. So the real change is a `def`, six
theorems and a comparator config, and renaming the `def` alone leaves the library incoherent: a
`sortedEigenvalues` definition with a `sortedEig` theorem family around it, which is worse than the
abbreviation was.

**Whoever takes this must claim `comparator/*.json` as part of the lane.** Note also that the
declaration-name-drift gate **passes** in the half-renamed state, because the comparator entry it
checks is still literally correct — the gate compares pinned names against the build, and an
incoherent-but-consistent pair of names is invisible to it. Coherence of a name *family* is not
something any current gate measures.

## 9. `leftSingularVector` — total, with a junk value, but with real mitigations

**Location:** `ForTauCeti/Analysis/InnerProductSpace/Singular/System.lean:71` (77 references)

The definition is `σᵢ⁻¹ • A vᵢ`, and its own docstring says: "At a zero singular value this
definition evaluates to zero because division in a field is total." A singular vector is by
definition a unit vector, so at `σᵢ = 0` the name is false of the value.

**This is deliberately *not* filed as a defect, and the reasons matter more than the finding.**
Two mitigations are real: the surrounding API never asserts anything false — orthonormality is
stated on the *subtype of nonzero singular values*
(`orthonormal_leftSingularVector_subtype`, `selfCompAdjoint_apply_leftSingularVector`) — and the
same name for the same total construction is already used for matrices in the vendored
`lean-stat-learning-theory` excerpt, so a rename here diverges from an outside precedent.

**Severity: document, do not rename.** The docstring already discloses the junk value; that is the
correct fix for a total definition whose theorems are all guarded. Recorded here so the next
auditor does not re-open it, and so that a reviewer who *does* raise it gets this answer rather than
a rediscovery.

## Status

| item | status |
|---|---|
| 6. `IsBddMeasurable.bound` | **open** — rename to `chooseBound`; contradicts this document's own resolved convention |
| 7. `permEV` | **open** — rename to `permuteCoords`; 19 refs, mechanical |
| 8. `sortedEig` | **open, and larger than it looks** — the `def` plus six theorem names plus a pinned comparator entry; must be claimed together, see the correction in the section |
| 9. `leftSingularVector` | **closed, deliberately** — junk value is real but disclosed and the guarded API is honest |

---

# Names that do not materially overclaim

## Finite-dimensional Courant-Fischer

A declaration named `courantFischer` under explicit finite-dimensional assumptions is an honest standard form of the Courant-Fischer theorem. The existence of compact-operator or discrete-spectrum variants does not make the finite theorem misnamed.

Recommended action:

- keep the mathematical name;
- mention "finite-dimensional" prominently in module documentation;
- optionally use a `FiniteDimensional` namespace if not already present.

## Finite-dimensional Eckart-Young

The equality between approximation numbers and singular values for finite-dimensional maps is genuinely an Eckart-Young theorem.

Recommended action:

- keep the name;
- do not imply that compact-operator Eckart-Young is already formalized;
- add the compact version to the roadmap rather than weakening the existing name.

## `moorePenroseInverse`

The object is explicitly defined in a finite-dimensional namespace from singular data. The name is mathematically appropriate even though only part of its characterization has been proved.

Recommended action:

- keep `moorePenroseInverse`;
- complete the remaining Penrose equations and uniqueness later;
- remove the misleading `inverseOnRange` compatibility layer.

## Finite-dimensional Schatten norm

A function computing the `ℓᵖ` norm of the finite singular-value vector is legitimately a finite-dimensional Schatten norm.

Recommended action:

- keep the name when finite-dimensional assumptions are visible;
- do not name the module or documentation as though full infinite-dimensional Schatten ideals, completeness, trace-class theory, and duality were already present.

## Source theorem numbers

Names such as `theorem63...` or `section7...` are source-facing correspondence names, not claims that the declaration is the most general modern theorem. These may remain in the Davis-Kahan source namespace provided:

- corrected hypotheses are visible;
- partial results carry `_partial`;
- finite specializations carry `_finite` or equivalent;
- false printed statements are not silently exposed under the source theorem name.

---

# Optional Mathlib-style polish

The following are not correctness blockers. They would merely make hypotheses more visible.

| Current style | More explicit style |
|---|---|
| `polar_decomposition_of_isUnit` | already good |
| `polarUnitaryEquiv` | `polarUnitaryEquivOfIsUnit` |
| `moorePenroseInverse_comp_eq_id_of_injective` | already good |
| `isUnit_modulus_of_norm_adjoint_comp_self_sub_one_lt_one` | already honest, though long |
| `comp_moorePenroseInverse_comp` | `comp_moorePenroseInverse_comp_eq_self` |
| `comp_moorePenroseInverse_comp_eq_of_ker_le` | already conclusion-oriented enough |

Do not perform large churn merely to normalize style when the existing name already states the mathematical content accurately.

---

# Recommended action order

## Before the initial approximation-number PR

No rename in this audit blocks the approximation-number PR.

Confirm only that:

- finite-dimensional results remain visibly finite-dimensional;
- no broad Schatten-ideal claim appears in the PR description;
- the exported approximation-number API does not depend on the `UnitaryInvariantIdealFamily` alias.

## Before the polar-decomposition PR

1. Replace or rename `ContinuousLinearMap.polarIsometry`.
2. Rename `polarUnitary` to make its noncanonical choice explicit.
3. Prefer an existential theorem for the singular unitary extension.
4. Reserve canonical `polarFactor` or `polarPartialIsometry` names for the general partial-isometry object.

## Before the Moore-Penrose PR

1. Remove `inverseOnRange` as a total-map alias.
2. Define an actual range-domain inverse if downstream code needs one.
3. Keep `moorePenroseInverse`.
4. Add the remaining Penrose equations and uniqueness to the roadmap.

## Before the ideal-family PR

1. Remove `UnitaryInvariantIdealFamily := KyFanDominantIdealFamily`.
2. Use `KyFanDominantIdealFamily` explicitly.
3. Later split the broad ideal-family structure from a `HasKyFanDominance` capability.

## Before the infinite-dimensional tan-two-theta PR

1. Rename the module and declarations to expose the finite active carrier.
2. Reserve `_infinite` or unsuffixed names for the genuinely unrestricted Hilbert-space theorem.

---

# Roadmap entries

The following full-strength endpoints should be recorded without blocking honest partial APIs:

- general polar decomposition with canonical partial isometry;
- uniqueness and support projections for the polar factor;
- complete finite-dimensional Penrose characterization;
- closed-range infinite-dimensional Moore-Penrose inverse;
- broad symmetric/unitarily invariant ideal family separated from Ky Fan dominance;
- proof that standard ideal constructions satisfy Fan dominance;
- unrestricted infinite-dimensional sharp tan-two-theta theorem;
- compact-operator Courant-Fischer and Eckart-Young;
- infinite-dimensional Schatten ideals and their analytic structure.

---

# Final assessment

Yes, the repository currently has names that claim more than their implementations warrant. The serious cases are limited and identifiable; this is not a pervasive flaw.

The declarations that should be corrected before their own Tau Ceti PRs are:

```text
ContinuousLinearMap.polarIsometry
TauCeti.polarUnitary
FiniteDimensional.inverseOnRange
UnitaryInvariantIdealFamily
the *_infinite tan-two-theta family
```

The initial approximation-number PR is not blocked by this audit. Most other famous theorem names are honest standard restricted forms, and their stronger variants belong on the roadmap rather than forcing premature renames.
