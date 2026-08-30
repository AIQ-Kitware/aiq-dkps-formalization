BASE HEAD: `0512e8f0e217161bc6812fdaf7f166da95450f9c`
FINAL HEAD: `0512e8f0e217161bc6812fdaf7f166da95450f9c`

Standalone extraction inspected for comparison: `28f227ee6977bd4360cf4a8b49393d8adfa3df3b`.

The production repository was clean at the start and remains clean. I did not edit it because this environment has no `lean`, `lake`, or `elan`, no populated `.lake`, and outbound DNS is unavailable, so I could not compile theorem-interface changes. Given the requested build discipline, I did not leave uncompiled API edits.

The main conclusion is **yes**: the full unbounded Davis–Kahan API can be materially cleaner than it is now. Some of the current complexity is intrinsic mathematics, but some is proof infrastructure leaking through the public theorem boundary. `HasUnboundedSylvesterKyFan` is the clearest example. The repository already proves the mathematical result represented by that class for both scalar fields Davis–Kahan uses. It does not need to be a hypothesis of a public real or complex sine-theta theorem.

## A. Current theorem surfaces

### 1. sin Θ

There are currently two competing notions of “canonical”.

The presentation/audit declaration is:

`DavisKahan1970.sinTheta_headline`

Its source declaration is:

```lean
theorem sinTheta_headline
    [ContinuousLinearMap.HasMinMaxLowerBoundEverywhere.{u, v} 𝕜]
    [HasUnboundedSylvesterKyFan.{u, v} 𝕜]
    (N : UnitaryInvariantNorm)
    (A : E →ₗ.[𝕜] E)
    (A₀ : F →ₗ.[𝕜] F)
    (Λ₁ : G →ₗ.[𝕜] G)
    (E₀ : F →L[𝕜] E)
    (F₀ : H →L[𝕜] E)
    (F₁ : G →L[𝕜] E)
    (sinTheta₀ : F →L[𝕜] E)
    (R : F →L[𝕜] E)
    (hSinTheta₀ :
      sinTheta₀ =
        (ContinuousLinearMap.id 𝕜 E - F₀ ∘L F₀.adjoint) ∘L E₀)
    (hA : IsSelfAdjoint A)
    (hA₀ : IsSelfAdjoint A₀)
    (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidual A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {β α δ : ℝ}
    (hβα : β ≤ α)
    (hδ : 0 < δ)
    (hspectral :
      (LinearPMap.realSpectrum A₀ ⊆ Set.Icc β α ∧
          LinearPMap.realSpectrum Λ₁ ⊆
            {x : ℝ | x ≤ β - δ ∨ α + δ ≤ x}) ∨
        (LinearPMap.realSpectrum Λ₁ ⊆ Set.Icc β α ∧
          LinearPMap.realSpectrum A₀ ⊆
            {x : ℝ | x ≤ β - δ ∨ α + δ ≤ x}))
    (hR : N.Mem R) :
    δ * N.gauge sinTheta₀ ≤ N.gauge R
```

This is arbitrary-dimensional and unbounded, but its own type only exposes the finite interval/exterior separation branch. It also leaks two scalar-field capability classes.

The stronger reusable engine is:

`TauCeti.DavisKahan1970.sinTheta_unbounded_exact_generic`

with `FormBoundedSylvesterGap`, which additionally covers the ordered half-line configurations required by the Appendix. The fixed-field public aliases

`TauCeti.DavisKahan1970.sinTheta`
`TauCeti.DavisKahan1970.sinTheta_real`

route to `FormBoundedIsometricSinThetaProblem.result_complex` and `.result_real`. These remove the two capability assumptions, but bundle almost the entire theorem setup into `FormBoundedIsometricSinThetaProblem`.

So there is currently **no one direct, source-shaped declaration with both the clean direct argument list and the complete unbounded gap scope**.

**Verdict:** API leakage. This is the easiest headline to fix.

---

### 2. tan Θ

The declaration named

`TauCeti.DavisKahan1970.tanTheta_headline_generic_directed`

is finite-dimensional. It is therefore not the full theorem despite its name.

The strongest unbounded directed theorem is currently the complex

`TauCeti.DavisKahan.ExactTanTheta.UnboundedCompressionTrialData.ideal_of_reducing_exists`

and its real counterpart. Its important part is:

```lean
theorem ideal_of_reducing_exists
    (N : KyFanDominantIdealFamily ℂ)
    (A : H →ₗ.[ℂ] H)
    {α δ : ℝ} (hδ : 0 < δ)
    (hZA : ∀ z : D.compression.domain, ((z : Z) : H) ∈ A.domain)
    (haction : ∀ z : D.compression.domain,
      D.action z = A ⟨((z : Z) : H), hZA z⟩)
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : H)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A x) =
        A ⟨Vᗮ.starProjection ((x : H)), hVdom x⟩)
    (hupper : LinearPMap.SemiboundedAbove D.compression α)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (α + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (hResidual : N.Mem D.residual) :
    ∃ tanTheta0 : Z →L[ℂ] H,
      HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0 ∧
      N.Mem tanTheta0 ∧
      δ * N.gauge tanTheta0 ≤ N.gauge D.residual
```

The strongest source-facing unbounded ambient complex declaration is:

`TauCeti.DavisKahan1970.tanTheta_unboundedCompression_ambient_paperUINorm_exact`

with real sibling

`tanTheta_unboundedCompression_ambient_paperUINorm_real_exact`.

It permits the Ritz compression itself to be unbounded:

```lean
theorem tanTheta_unboundedCompression_ambient_paperUINorm_exact
    (N : PaperUnitaryInvariantNorm)
    {U V : Submodule ℂ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (D : UnboundedCompressionTrialData U)
    (A : E →ₗ.[ℂ] E)
    (H : E →L[ℂ] E) (hH : IsSelfAdjoint H)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hZA : ∀ z : D.compression.domain, ((z : U) : E) ∈ A.domain)
    (haction : ∀ z : D.compression.domain,
      D.action z = A ⟨((z : U) : E), hZA z⟩)
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : E)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A x) =
        A ⟨Vᗮ.starProjection ((x : E)), hVdom x⟩)
    (hupper : LinearPMap.SemiboundedAbove D.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (h35 : DavisKahan.CrossedDefectsEquivalent U V)
    (hResidual :
      D.residual = Uᗮ.starProjection ∘L H ∘L U.subtypeL)
    (hMem : N.Mem H) :
    N.Mem (paperTanAngleOperatorC U V) ∧
      delta * N.gauge (paperTanAngleOperatorC U V) ≤ N.gauge H
```

The important positive point is that this theorem already concludes in terms of the literal canonical `paperTanAngleOperatorC`. The tangent operator is not caller-supplied.

The remaining problem is the Ritz-data interface. `hZA`, `haction`, `hVdom`, and `hVcomm` expose the interface between a generic unbounded compression bundle and the ambient operator.

**Verdict:** the mathematics is present and source-faithful, but the public construction interface is too low-level. No missing Sylvester theorem blocks cleanup.

---

### 3. sin 2Θ

Again,

`sinTwoTheta_headline_generic_directed`

is a finite-dimensional facade.

The full unbounded directed complex source theorem is:

`TauCeti.DavisKahan1970.sinTwoTheta_unbounded_directedResidual_paperUINorm`

with real sibling. It correctly has the paper residual as the right-hand side and constructs the reflection argument internally.

Its conclusion, however, is:

```lean
N.Mem
  (sinTwoThetaIdealBlock
    (selfAdjointSpectralSubspace A hA B hB) V) ∧
δ * N.gauge
  (sinTwoThetaIdealBlock
    (selfAdjointSpectralSubspace A hA B hB) V)
  ≤ 2 * N.gauge R
```

The full unbounded ambient complex theorem already exists at the generic ideal layer:

`TauCeti.DavisKahan.sinTwoTheta_addBounded_unitaryInvariant_of_spectrum_gap`

and handles arbitrary dimension, unbounded `A`, bounded self-adjoint perturbation, and arbitrary Ky-Fan-dominant symmetric ideal family.

There is also:

`TauCeti.DavisKahan1970.sinTwoTheta_addBounded_paperUINorm_real`

for real scalars.

I found **no corresponding complex `sinTwoTheta_addBounded_paperUINorm` wrapper**. That is a small concrete source-API omission: the stronger generic complex theorem is already there.

The larger issue is the conclusion object. The repository already defines the mathematically literal

`paperSinTwoAngleOperatorC U V := cfc (fun t => sin (2*t)) (paperAngleOperatorC U V)`

but the unbounded ideal theorem exposes `sinTwoThetaIdealBlock`, an overlap-with-reflected-complement block used by the proof.

**Verdict:** the theorem is mathematically complete, but its conclusion exposes a proof representation rather than the source's canonical angle operator. A missing wrapper is cheap; replacing the block in every UI norm requires a reusable ideal-level principal-angle transport theorem.

---

### 4. tan 2Θ

The generic `tanTwoTheta_headline_generic` is also only a bounded/finite facade.

The actual unbounded endpoints are:

`TauCeti.DavisKahan1970.tanTwoTheta_unbounded_directedResidual_paperUINorm_exact`
`TauCeti.DavisKahan1970.tanTwoTheta_unbounded_directedResidual_paperUINorm_real_exact`
`TauCeti.DavisKahan1970.tanTwoTheta_unbounded_ambient_paperUINorm_exact`
`TauCeti.DavisKahan1970.tanTwoTheta_unbounded_ambient_paperUINorm_real_exact`.

The complex ambient type is:

```lean
theorem tanTwoTheta_unbounded_ambient_paperUINorm_exact
    (N : PaperUnitaryInvariantNorm)
    {A : G →ₗ.[ℂ] G} {B Z : G →L[ℂ] G} {a b c : ℝ}
    (hA : IsSelfAdjoint A)
    (hBsa : IsSelfAdjoint B)
    (hB : TauCeti.IsOddFor
      (LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) B)
    (hZsa : IsSelfAdjoint Z)
    (hZ2 : Z * Z = 1)
    (hZdom : LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : G), hZdom x⟩ + B (Z (x : G)) =
        Z (A x) + Z (B (x : G)))
    (hUa : ...)
    (hUb : ...)
    (hab : a < b)
    (hBmem : N.Mem B) :
    IsUnit (U.diagonalPart Z * U.diagonalPart Z) ∧
      N.Mem (unboundedReflectionTangent U Z) ∧
      (b - a) * N.gauge (unboundedReflectionTangent U Z)
        ≤ 2 * N.gauge B
```

where `U` is the low spectral range written explicitly in the actual type.

Several good choices are already visible here:

* pole exclusion is **concluded**, not caller-supplied;
* no finite-dimensionality or compactness premise appears;
* no extra spectral-location condition for the perturbed projection is imposed;
* the factor is exactly two.

But `Z` and four facts describing it are caller inputs. In the mathematical theorem, `Z` is the reflection associated with the perturbed reducing/spectral subspace. Likewise, `unboundedReflectionTangent U Z` is a block-algebra proof representative, not the natural object an operator theorist starts with.

**Verdict:** substantial representation leakage remains in the public full-scope type.

---

### Overall current-surface verdict

The repository has full mathematical coverage, but the accepted source scope is reconstructed from a family of declarations:

* presentation facades,
* full unbounded companions,
* directed and ambient companions,
* real/complex companions.

For three of the four results, the declaration most naturally found by its “headline” name does not itself state the full theorem. That is an API problem independent of Palomar.

## B. `HasUnboundedSylvesterKyFan`

### Definition in mathematics

`HasUnboundedSylvesterKyFan 𝕜` says:

For every pair of complete Hilbert spaces over `𝕜`, every pair of self-adjoint possibly unbounded `LinearPMap`s `A` and `B`, every bounded `X` and `C`, and every positive `δ`, if

1. `A` and `B` satisfy `FormBoundedSylvesterGap A B δ`, and
2. the domain-aware Sylvester equation
   `A X - X B = C`
   holds,

then for every finite Ky Fan gauge,

`δ · KyFan_k(X) ≤ KyFan_k(C)`.

That is the sharp unbounded Sylvester estimate, not a primitive property of a Davis–Kahan problem.

### Source correspondence

Davis–Kahan does not assume this as an additional hypothesis of sin Θ.

The repository's source transcription places this analysis in Section 5 / Appendix 6: spectral separation is used to prove the Sylvester estimate, which is then used in the Section 2 perturbation theorem.

### Constructors

The class has both required instances:

* `hasUnboundedSylvesterKyFan_complex`, obtained from `davisKahan1970_sylvester_complex`;
* `hasUnboundedSylvesterKyFan_real`, obtained from `real_unbounded_sylvester_kyFan`.

The complex constructor specializes the already-proved full unbounded Sylvester theorem to each Ky Fan ideal. The real constructor uses the proved complexification descent.

### Consumers

Direct production consumers are almost entirely the scalar-generic sine-theta machinery:

* `unbounded_sylvester_kyFan`;
* `SineTheta/CommonDomainSymmetric.lean`;
* `SineTheta/HeadlineGeneric.lean`;
* `SineTheta/PaperSurface.lean`.

This is exactly the pattern expected from a proof-routing capability rather than user-supplied theorem data.

### Classification

**E — proof capability / implementation witness**, backed by a **B — reusable generic theorem**.

It is not A, a Davis–Kahan source hypothesis.

It is not circular: the class packages the independent Sylvester estimate, not the final sine-theta estimate. But asking a caller to supply it still factors the public theorem at the wrong boundary.

### Can it be derived today?

For the actual source scalar fields, **yes**.

For `ℂ`, it is already proved directly.
For `ℝ`, it is already proved by complexification.

There is therefore **no missing analytic theorem blocking a clean complex or real source-facing sin Θ declaration today**.

The only thing preventing removal from an arbitrary

```lean
{𝕜} [RCLike 𝕜]
```

theorem is that `RCLike` is an open abstraction: Lean cannot prove a proposition for every possible `RCLike` instance merely from separate proofs for `ℝ` and `ℂ`.

That is a scalar-generic API issue. It is not part of Davis–Kahan mathematics.

The clean public choice is consequently:

* canonical complex theorem;
* canonical `_real` theorem;
* retain the `RCLike` capability-driven theorem as a lower-level generic engine.

The same conclusion applies to `ContinuousLinearMap.HasMinMaxLowerBoundEverywhere`: it has proved complex and real instances and should not be visible in fixed-field headline signatures.

## C. UI norm abstraction

The earlier suggestion that the public norm could be replaced by

* a function `N`,
* subadditivity,
* absolute homogeneity,
* left/right unitary invariance

is too weak for the source-level infinite-dimensional theorem.

`PaperUnitaryInvariantNorm` contains:

```lean
structure PaperUnitaryInvariantNorm where
  finiteNorm : ∀ n,
    UnitarilyInvariantSeminorm ℂ (EuclideanSpace ℂ (Fin n))
  normalized : ...
  zero_pad : ...
```

The important additional content is dimension coherence through `zero_pad`, plus normalization.

Its infinite-dimensional interpretation is then derived canonically:

```lean
extendedGauge N A =
  ⨆ n, ENNReal.ofReal (N.prefixGauge n A)

N.Mem A := N.extendedGauge A ≠ ⊤

N.gauge A := (N.extendedGauge A).toReal
```

So ideal membership is not an arbitrary additional structure selected by the caller. It is the domain on which the source norm generated by the finite-dimensional norming function is finite.

This matches the repository's source interpretation substantially better than an unconstrained norm functional on all bounded operators.

The generic lower layer is:

* `SymmetricOperatorIdealFamily`;
* completeness of its ideal;
* `TauCeti.IsKyFanDominant`;
* approximation-number/Ky Fan infrastructure.

`KyFanDominantIdealFamily` is currently a convenient local package of that data.

### Recommendation

Keep both levels, with different roles.

**Source-facing theorem:** quantify over `PaperUnitaryInvariantNorm`.

**Reusable operator-theory theorem:** quantify over the canonical symmetric ideal-family abstraction, plus the necessary completeness/Fan-dominance properties.

Do not put both spellings in one headline signature.

`N.Mem R` or `N.Mem H` is genuine mathematics in infinite dimension: a general UI norm is finite on its associated ideal rather than on every bounded operator.

## D. Other leaked objects

| Object                                              | Classification                           | Reason                                                                                                                                                                                                                                                                          |
| --------------------------------------------------- | ---------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `UnboundedTrialBlock`                               | **RENAME / HIDE from the full headline** | It bundles a bounded Ritz compression and residual, both already determined by `A` and the trial subspace once their bounded extensions exist. Useful lower-level bounded-compression object, but it does not represent the Appendix's most general unbounded Ritz compression. |
| `UnboundedCompressionTrialData`                     | **KEEP, improve constructors**           | This is closer to a genuine unbounded Ritz pair: self-adjoint unbounded compression plus bounded orthogonal residual. The ambient-domain/action relationship should preferably be constructible rather than supplied as several loose arguments.                                |
| `paperTanAngleOperatorC`                            | **KEEP**                                 | Canonical source quantity: functional calculus `tan Θ`, determined entirely by the two subspaces. The strongest ambient tan Θ theorem already uses it correctly.                                                                                                                |
| `sinTwoThetaIdealBlock`                             | **HIDE / REPLACE on source surface**     | `P_U P_{J_V(U⊥)}` is an excellent proof vehicle for symmetric ideals but is not the literal `sin 2Θ` object exposed by the paper.                                                                                                                                               |
| `unboundedReflectionTangent`                        | **HIDE / REPLACE on source surface**     | Totalized block-algebra implementation of `tan 2Θ`; depends on caller-supplied reflection `Z`. Keep as proof infrastructure.                                                                                                                                                    |
| `Z` plus `hZsa`, `hZ2`, `hZdom`, `hZcomm` in tan 2Θ | **DERIVE**                               | A reducing/spectral subspace `V` canonically determines its reflection, and the corresponding properties should follow from the reducing-domain API.                                                                                                                            |
| `CrossedDefectsEquivalent` in ambient tan Θ         | **KEEP**                                 | This is the formalization of the documented nonlocal standing condition (3.5). It is source semantics, not leakage.                                                                                                                                                             |
| `IsTrialResidual`                                   | **KEEP**                                 | Small, readable packaging of the source Ritz map/domain/residual equation.                                                                                                                                                                                                      |
| `IsExactSpectralDecomposition`                      | **KEEP**                                 | Small source-facing representation of the exact subspace/complement decomposition and intertwining.                                                                                                                                                                             |

## E. Proposed canonical API

I would stop trying to make the four canonical source declarations scalar-generic over arbitrary `RCLike`. Use complex canonical declarations and explicit `_real` siblings, while retaining generic engines underneath.

### sin Θ

The first production target should be approximately:

```lean
theorem sinTheta
    (N : PaperUnitaryInvariantNorm)
    (A : E →ₗ.[ℂ] E)
    (A₀ : F →ₗ.[ℂ] F)
    (Λ₁ : G →ₗ.[ℂ] G)
    (E₀ : F →L[ℂ] E)
    (F₀ : H →L[ℂ] E)
    (F₁ : G →L[ℂ] E)
    (R : F →L[ℂ] E)
    (hA : IsSelfAdjoint A)
    (hA₀ : IsSelfAdjoint A₀)
    (hΛ₁ : IsSelfAdjoint Λ₁)
    (htrial : IsTrialResidual A A₀ E₀ R)
    (hexact : IsExactSpectralDecomposition A Λ₁ F₀ F₁)
    {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap A₀ Λ₁ δ)
    (hR : N.Mem R) :
    N.Mem ((1 - F₀ ∘L F₀.adjoint) ∘L E₀) ∧
      δ * N.gauge ((1 - F₀ ∘L F₀.adjoint) ∘L E₀)
        ≤ N.gauge R
```

and the same for `sinTheta_real`.

This has the complete source gap scope and neither capability class.

A convenience `sinTheta_of_intervalExterior` can spell out the familiar Section 2 interval form.

### tan Θ

The theorem should take a real mathematical Ritz object rather than several implementation connections:

```lean
theorem tanTheta
    (N : PaperUnitaryInvariantNorm)
    (D : UnboundedRitzData A U)
    (V : Submodule ℂ E)
    ...
    (hupper : SemiboundedAbove D.compression α)
    (hUnwanted : ...)
    (h35 : CrossedDefectsEquivalent U V)
    (H : E →L[ℂ] E)
    (hH : IsSelfAdjoint H)
    (hResidual : D.residual = P_Uperp ∘ H ∘ inclusion_U)
    (hHmem : N.Mem H) :
    N.Mem (paperTanAngleOperatorC U V) ∧
      δ * N.gauge (paperTanAngleOperatorC U V)
        ≤ N.gauge H
```

`UnboundedRitzData.ofCompression` / `.ofTrialSubspace` should construct the domain/action relations.

The directed theorem should be a nearby systematic sibling rather than living under a different proof namespace.

### sin 2Θ

At the source surface:

```lean
theorem sinTwoTheta
    (N : PaperUnitaryInvariantNorm)
    (A : E →ₗ.[ℂ] E)
    (hA : IsSelfAdjoint A)
    (H : E →L[ℂ] E)
    (hH : IsSelfAdjoint H)
    (U : exact spectral subspace of A)
    (V : selected spectral subspace of A.addBounded H)
    {δ : ℝ}
    (hδ : 0 < δ)
    (hgap : source spectral separation ...)
    (hHmem : N.Mem H) :
    N.Mem (paperSinTwoAngleOperatorC U V) ∧
      δ * N.gauge (paperSinTwoAngleOperatorC U V)
        ≤ 2 * N.gauge H
```

The current `sinTwoThetaIdealBlock` theorem remains the proof engine.

The direct residual version should similarly conclude on the canonical directed `sin 2Θ₀` representation.

### tan 2Θ

The source theorem should start from the two spectral/reducing subspaces, not a reflection witness:

```lean
theorem tanTwoTheta
    (N : PaperUnitaryInvariantNorm)
    (A : E →ₗ.[ℂ] E)
    (hA : IsSelfAdjoint A)
    (H : E →L[ℂ] E)
    (hH : IsSelfAdjoint H)
    (U : low spectral subspace of A)
    (V : selected reducing/spectral subspace of A.addBounded H)
    (hOffDiagonal : IsOddFor U H)
    (hgap : ordered spectral/form gap ...)
    (hHmem : N.Mem H) :
    NoTanTwoPole U V ∧
      N.Mem (paperAbsTanTwoAngleOperatorC U V) ∧
      δ * N.gauge (paperAbsTanTwoAngleOperatorC U V)
        ≤ 2 * N.gauge H
```

If the literal signed `paperTanTwoAngleOperatorC` is appropriate after the derived pole theorem, expose that as a corollary.

The reflection

```lean
Z := V.reflectionOperator
```

and its self-adjointness, involution, domain preservation, and commutation should be internal.

## F. Implementation performed

No source changes and no commits.

I deliberately stopped before editing because the sandbox cannot run the repo's Lean toolchain. An API redesign of theorem types without a compiler checkpoint would violate the requested workflow.

The first two implementation commits I would make in a working checkout are sharply bounded:

1. **Source-facing sin Θ API**

   * add complex and real direct-argument full-`FormBoundedSylvesterGap` declarations;
   * route them through the already proved fixed-field unbounded theorem;
   * no `HasUnboundedSylvesterKyFan`;
   * no `HasMinMaxLowerBoundEverywhere`;
   * retain generic capability-driven theorem below them.

2. **Complex sin 2Θ PaperUI wrapper**

   * add the missing complex counterpart of `sinTwoTheta_addBounded_paperUINorm_real`;
   * simply adapt `PaperUnitaryInvariantNorm` to the already proved complex generic ideal theorem.

Neither requires new analytic mathematics.

## G. Reusability demonstration

The target user experience for sin Θ should be roughly:

```lean
import DavisKahan.Sources.DavisKahan1970.Section2

open TauCeti DavisKahan1970

have h :=
  sinTheta
    TauCeti.SymmetricIdeal.paperOperatorNorm
    A A₀ Λ₁ E₀ F₀ F₁ R
    hA hA₀ hΛ₁
    htrial hexact
    hδ hgap hR
```

For a Hilbert–Schmidt/Frobenius-type source norm, the norm selection should change to the existing `paperLpNorm 2 ...`; the theorem interface should otherwise be unchanged.

A new user should only need to learn:

1. unbounded self-adjoint operators are `LinearPMap`s;
2. exact/trial spectral geometry uses subspaces/isometric maps;
3. the gap is `FormBoundedSylvesterGap`, with readable constructors;
4. perturbations and residuals are bounded continuous linear maps;
5. source norms are `PaperUnitaryInvariantNorm`s;
6. infinite-dimensional finiteness is `N.Mem`;
7. angle objects are constructed by the library.

They should not need to know `HasUnboundedSylvesterKyFan` or the reflection/block implementation of double angles.

## H. Palomar impact

I could not reproduce the earlier compiler-derived transitive constant closure because Lean is unavailable here. I therefore do not present the old approximately-206-constant count as a fresh measurement.

I did make fresh source-level measurements at HEAD:

| Current declaration                             |   theorem-header size |
| ----------------------------------------------- | --------------------: |
| `sinTheta_headline`                             | 32 lines / 1019 chars |
| `sinTheta_unbounded_exact_generic`              |  19 lines / 774 chars |
| unbounded ambient `tanTheta` complex            | 24 lines / 1104 chars |
| unbounded directed `sinTwoTheta` complex        |  17 lines / 880 chars |
| unbounded ambient generic `sinTwoTheta` complex | 23 lines / 1143 chars |
| unbounded ambient `tanTwoTheta` complex         | 27 lines / 1331 chars |

These are textual surface measurements, not Lean dependency-closure counts.

The proposed cleanup would materially improve Palomar extractability for the right reason:

* two proof-capability classes disappear from sin Θ;
* source scope no longer has to be reconstructed from a finite “headline” plus unbounded companions;
* `Z`, `sinTwoThetaIdealBlock`, and `unboundedReflectionTangent` disappear from trusted source theorem statements;
* the remaining non-Mathlib vocabulary is mostly actual reusable operator theory.

Palomar would still face an external dependency problem because current released Tau Ceti does not yet contain the required unbounded spectral theory, operator ideals, approximation numbers, and principal-angle infrastructure. That would then be a clean upstream-library boundary rather than a malformed Davis–Kahan API.

## I. Upstream map

The generic pieces line up well with the pending Tau Ceti roadmap.

**Majorization**

* finite-dimensional UI seminorms;
* symmetric norming functions/gauges;
* majorization and Fan dominance.

**OperatorIdeals**

* approximation singular values;
* Ky Fan gauges;
* `SymmetricOperatorIdealFamily`;
* ideal completeness;
* `IsKyFanDominant`;
* Schatten/Hilbert–Schmidt/nuclear/operator-norm standard families.

**PrincipalAngles / OrthogonalGeometry**

* `paperAngleOperator`;
* sine/tangent/double-angle operators;
* projection-gap identities;
* reflection/direct-rotation geometry;
* crossed-defect equivalence;
* ideal-level equivalence between canonical angle operators and proof blocks.

**SelfAdjointSpectralTheory**

* `LinearPMap.realSpectrum`;
* `spectrum`;
* `specRange`;
* spectral restriction/subspace;
* semiboundedness;
* reducing subspaces with domain preservation;
* bounded perturbation of an unbounded self-adjoint operator.

**SpectralSubspacePerturbation**

* `FormBoundedSylvesterGap`;
* domain-aware Sylvester equation;
* the sharp unbounded Ky Fan Sylvester theorem currently hidden behind `HasUnboundedSylvesterKyFan`;
* reusable Ritz/subspace perturbation machinery.

**DavisKahan**

* `PaperUnitaryInvariantNorm` as source terminology;
* `IsTrialResidual`;
* `IsExactSpectralDecomposition`;
* Section 3 standing-condition disclosure;
* four source-named headline theorem families and their real siblings.

## J. Remaining blocker

The Sylvester theorem is **not** the remaining mathematical blocker. It is already proved.

The single most important reusable result still needed to make all four source surfaces clean is an **arbitrary-Hilbert symmetric-ideal principal-angle representation theorem**:

> For two closed subspaces, the canonical `sin 2Θ` / branch-free `tan 2Θ` operators have the same approximation-singular-value data, hence the same membership and gauge in every symmetric unitary-invariant ideal, as the reflection/block representatives used by the unbounded proofs; the reflection used in the tangent representation is constructed canonically from the second reducing subspace.

That bridge would let `sinTwoThetaIdealBlock` and `unboundedReflectionTangent` remain internal while the full unbounded source theorems conclude on the literal paper angle objects.

For sin Θ, no corresponding blocker exists: a cleaner full-scope public theorem can be assembled from results already present.

### Final assessment

`HasUnboundedSylvesterKyFan` is a generic theorem packaged as a scalar-field capability and then exposed through a headline interface. For Davis–Kahan's actual scalar fields it is proof infrastructure, not theorem data.

The current API therefore falls under **Outcome A — API leakage**, with a smaller amount of **Outcome B — missing reusable principal-angle transport/API infrastructure** affecting the cleanest double-angle presentation.

The intrinsic complexity that should survive is narrower:

* unbounded self-adjoint `LinearPMap`s and their domains;
* a genuine spectral-gap abstraction;
* domain-aware Ritz/reducing data;
* a coherent infinite-dimensional symmetric ideal/UI norm with membership;
* the tangent theorem's crossed-dimension standing condition.

The public API does not need to expose the existence of the Sylvester proof engine, a min-max implementation capability, caller-built reflections, or internal double-angle blocks.

The highest-value next change is therefore the direct complex/real full-gap `sinTheta` pair. It requires no new Davis–Kahan mathematics and gives a concrete model for how the other three canonical declarations should be organized.

