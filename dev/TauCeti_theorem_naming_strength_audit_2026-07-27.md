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
ForTauCeti/Analysis/InnerProductSpace/PolarIsometry.lean
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
ForTauCeti/Analysis/InnerProductSpace/PolarDecomposition.lean
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

The definition `moorePenroseInverse` itself is honest: it is explicitly finite-dimensional and computes the standard pseudoinverse. The API is incomplete, but the name does not claim that all four Penrose equations have already been proved.

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
