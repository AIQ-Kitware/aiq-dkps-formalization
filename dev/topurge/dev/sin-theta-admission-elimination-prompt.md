# Task: eliminate every admission from the source-facing sine-theta theorem

## Environment

- Repository: `~/code/aiq-dkps-formalization`, branch `main`.
- A **working Lean toolchain and a fully built Mathlib cache are present**. You
  are expected to compile. `lake build` completes clean at HEAD; every
  regression you introduce is your own.
- Read `AGENTS.md` first. Two rules bind you absolutely:
  - Never write the literal words `sorry` or `axiom` in a comment or docstring.
    (A genuine incomplete proof term is code, not a comment — but see below:
    you may not leave any.)
  - Never claim a declaration is complete until Lean has accepted it.
- Do **not** introduce `sorry`, `admit`, `native_decide`, or new `axiom`
  declarations. Do not weaken a theorem statement to make it provable. Do not
  add a hypothesis that is not mathematically necessary.

## Goal

Make this declaration free of admissions:

```
ForMathlib.DavisKahan1970.sinTheta
  (= ForMathlib.DavisKahan.Experimental.ExactSinTheta.IsometricSinThetaProblem.result)
```

and likewise

```
ForMathlib.DavisKahan1970.generalizedSinTheta
  (= ...ExactSinTheta.GeneralSinThetaProblem.result)
ForMathlib.DavisKahan1970.generalizedSinTheta_boundedSpecialization
  (= ...ExactSinTheta.BoundedGeneralSinThetaProblem.result)
```

Success criterion, verbatim:

```lean
#print axioms ForMathlib.DavisKahan1970.sinTheta
-- must print exactly: [propext, Classical.choice, Quot.sound]
```

with no `sorryAx`, for all three names above.

## Verified diagnosis — read this before planning

This has already been machine-checked. Do not re-derive it; do verify it.

There are **two parallel API layers** for the unbounded sine-theta theorem:

| layer | gap predicate | spectrum notion | status |
|---|---|---|---|
| **legacy** | `UnboundedSylvesterGap` | `ClosedOperator.realSpectrum` | **DIRTY** |
| **genuine** | `GenuineUnboundedSylvesterGap` | `Spectra.Resolvent.spectrum` | **clean** |

The genuine layer is already fully proved and axiom-clean, end to end. The
source-facing aliases are still wired to the legacy layer. That is the whole
problem.

Machine-checked status of the chain (reproduce with `Lean.collectAxioms`):

```
DIRTY  UnboundedSylvesterGap                                   clean  GenuineUnboundedSylvesterGap
DIRTY  UnboundedIntervalExteriorGap                            clean  SylvesterIntervalExteriorGap
DIRTY  unbounded_sylvester_mem_and_gauge_le_of_gap             clean  unbounded_sylvester_mem_and_gauge_le_direct
DIRTY  unbounded_sylvester_mem_and_gauge_le_viaKyFan           clean  unbounded_sylvester_mem_and_gauge_le_direct_swapped
DIRTY  unbounded_sylvester_mem_and_gauge_le_swapped_viaKyFan   clean  davisKahan1970_sylvester_of_spectrumGap
DIRTY  unbounded_sylvester_mem_and_gauge_le_of_intervalExteriorGap
DIRTY  davisKahan1970_sylvester
DIRTY  generalizedSinTheta_unbounded                           clean  generalizedSinTheta_unbounded_of_spectrumGap
DIRTY  generalizedSinTheta_unbounded_exact                     clean  generalizedSinTheta_unbounded_exact_of_spectrumGap
DIRTY  GeneralSinThetaProblem.result                           clean  GenuineGeneralSinThetaProblem.result
DIRTY  IsometricSinThetaProblem.result                         clean  GenuineIsometricSinThetaProblem.result
DIRTY  BoundedGeneralSinThetaProblem.result                    clean  FiniteIntervalGeneralSinThetaProblem.result
DIRTY  ForMathlib.DavisKahanExt.ClosedOperator.realSpectrum    clean  Spectra.Resolvent.spectrum

clean  SemiboundedBelow / SemiboundedAbove / LowerFrameBound / UnboundedSinThetaData
clean  OrthogonalExactDecomposition / directedSinThetaOperator / sinThetaBlock
clean  sinThetaBlock_mem_and_gauge_eq_directedSinThetaOperator
```

### The single root cause

`DavisKahan/Experimental/InfiniteDimensional/Core/Unbounded.lean:540`

```lean
noncomputable def realSpectrum
    (A : ClosedOperator (𝕜 := 𝕜) (E := E)) : Set ℝ := by
  sorry
```

This is not merely an unproved theorem — it is an **unproved definition**.
Every legacy spectral hypothesis (`UnboundedIntervalExteriorGap`,
`SpectrumInRealSet`, `IntervalExteriorGap`, `boundedRealSpectrum`) is phrased
through it, so those statements are currently *meaningless*, not just unproven.
Fixing this is the highest-value single edit in the repository.

### Why this is tractable

Two decisive structural facts:

1. **The legacy ordered branches need no spectral theory at all.**
   `UnboundedSylvesterGap` (`Sylvester/Unbounded.lean:848`) has constructors:
   ```lean
   | leftAboveRightBelow (c : ℝ) (hA : SemiboundedBelow A (c + δ)) (hB : SemiboundedAbove B c)
   | leftBelowRightAbove (c : ℝ) (hA : SemiboundedAbove A c)       (hB : SemiboundedBelow B (c + δ))
   ```
   and the already-clean `directOrderedSylvesterEngine_lowerUpper` /
   `_upperLower` (`Sylvester/GenuineOrderedEngineDirect.lean`) take **exactly
   these hypotheses, verbatim**. These two branches are a direct substitution.

2. **The interval/exterior branch differs only by the spectrum notion.**
   ```lean
   -- legacy (Core/UnboundedSpectral.lean:620)
   (A.realSpectrum ⊆ Set.Icc β α ∧ B.realSpectrum ⊆ {x | x ≤ β - δ ∨ α + δ ≤ x}) ∨ (…swap…)
   -- genuine (Sylvester/GenuineAllGap.lean:39)
   (Spectra.Resolvent.spectrum A.toLinearPMap ⊆ Set.Icc β α ∧
     ∀ lam ∈ Set.Ioo (β - δ) (α + δ), lam ∉ Spectra.Resolvent.spectrum B.toLinearPMap) ∨ (…swap…)
   ```
   `{x | x ≤ β - δ ∨ α + δ ≤ x}` is exactly `(Set.Ioo (β - δ) (α + δ))ᶜ`. So
   once `realSpectrum` is *defined to be* the operator-theoretic spectrum, these
   two predicates are interconvertible by set logic plus one bridge lemma.

`ClosedOperator.toLinearPMap` already exists (`Core/Unbounded.lean:90`), with
`toLinearPMap_domain` and `toLinearPMap_apply` as `rfl` simp lemmas — so the
bridge to Spectra has no coercion obstacle.

## Work items

### Item 1 — define `realSpectrum` (REQUIRED, blocks everything)

`Core/Unbounded.lean:540`. Replace the admission with the standard
operator-theoretic definition, mirroring
`vendor/Spectra/Spectra/Resolvent/Spectrum.lean:49,58`:

```lean
/-- Reals `lam` for which `A - lam` has a two-sided bounded inverse. -/
def realResolventSet (A : ClosedOperator (𝕜 := 𝕜) (E := E)) : Set ℝ :=
  { lam : ℝ | ∃ R : E →L[𝕜] E,
      (∀ x : A.domain, R (A.toLinearMap x - (lam : 𝕜) • (x : E)) = (x : E)) ∧
      (∀ y : E, ∃ h : R y ∈ A.domain,
        A.toLinearMap ⟨R y, h⟩ - (lam : 𝕜) • R y = y) }

def realSpectrum (A : ClosedOperator (𝕜 := 𝕜) (E := E)) : Set ℝ :=
  (realResolventSet A)ᶜ
```

Constraints:
- **Keep the signature `(A : ClosedOperator …) : Set ℝ` exactly.** Many
  downstream files mention it; changing arity will cascade.
- Keep it generic over `RCLike 𝕜`. Do **not** restrict this definition to `ℂ`
  — `Core/Unbounded.lean` is a low-level generic module and `ℝ` instances
  depend on it.
- Do not add a `Spectra` import to `Core/Unbounded.lean`; that risks an import
  cycle. The bridge belongs in a higher module (Item 2).
- Match Spectra's shape **as closely as possible** so Item 2 is near-`rfl`.

Then check for fallout: `grep -rn "realSpectrum" DavisKahan/ --include=*.lean`.
Note there is a **second, unrelated** `realSpectrum` for *bounded* operators
(`DavisKahan.Experimental.Foundation.realSpectrum`, aliased in
`Core/Compatibility.lean:49`) used by `TanTwoTheta/BoundedOffDiagonal*.lean`.
Do not conflate them. If `boundedRealSpectrum` (which is
`(ClosedOperator.ofBounded A).realSpectrum`) now needs to agree with the
Foundation one, prove a compatibility lemma rather than redefining either.

### Item 2 — bridge to the genuine spectrum (REQUIRED, new declaration)

New lemma, in a module that already imports both (a new
`SpectraBridge/RealSpectrumBridge.lean` is the clean home):

```lean
theorem realSpectrum_eq_spectraSpectrum
    (A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)) :
    A.realSpectrum = Spectra.Resolvent.spectrum A.toLinearPMap
```

If Item 1 mirrors Spectra's definition faithfully this should reduce to
`Set.ext` plus unfolding both `resolventSet` definitions. Watch for exactly one
real mismatch: Spectra quantifies its resolvent condition over `z : ℂ` and
takes the real slice at the end, whereas ours is indexed by `lam : ℝ` directly.
Reconcile via `(lam : ℂ) • x`.

### Item 3 — gap converter (REQUIRED, new declaration)

```lean
theorem GenuineUnboundedSylvesterGap.of_legacy
    {A : ClosedOperator (𝕜 := ℂ) (E := E)} {B : ClosedOperator (𝕜 := ℂ) (E := F)}
    {δ : ℝ} (h : UnboundedSylvesterGap A B δ) :
    GenuineUnboundedSylvesterGap A B δ
```

Case on `h`:
- `intervalExterior` → rewrite both spectra with Item 2, convert
  `{x | x ≤ β - δ ∨ α + δ ≤ x}` membership into
  `∀ lam ∈ Set.Ioo (β - δ) (α + δ), lam ∉ …`. Pure set logic; `Set.mem_Ioo`,
  `not_lt`, `push_neg`.
- `leftAboveRightBelow` / `leftBelowRightAbove` → the genuine constructors are
  stated with *spectrum containment* (`⊆ Set.Ici (c + δ)`) while the legacy
  ones are stated with *form bounds* (`SemiboundedBelow A (c + δ)`). These are
  **not** interchangeable in this direction without work.
  **Therefore do not route the ordered branches through this converter** —
  see Item 4. Restrict Item 3 to the interval/exterior case, or return a
  disjunction the caller can dispatch on.

### Item 4 — reroute the legacy Sylvester engine (REQUIRED)

`Sylvester/Unbounded.lean`, `unbounded_sylvester_mem_and_gauge_le_of_gap` and
`davisKahan1970_sylvester`.

These are generic over `RCLike 𝕜`, but the genuine engine is `ℂ`-only. **Do not
attempt to make the generic version clean** — that would need a real-descent
argument that is out of scope. Instead add `ℂ`-specialized clean versions and
point the source-facing aliases at those:

```lean
theorem davisKahan1970_sylvester_complex
    (N : UnitaryInvariantIdealFamily (𝕜 := ℂ)) … (hgap : UnboundedSylvesterGap A B δ) … := by
  cases hgap with
  | intervalExterior hβα hgap =>
      -- Item 2 + Item 3, then davisKahan1970_sylvester_of_spectrumGap
  | leftAboveRightBelow c hAc hBc =>
      exact directOrderedSylvesterEngine_lowerUpper N hA hB hδ hAc hBc hEq hR
  | leftBelowRightAbove c hAc hBc =>
      exact directOrderedSylvesterEngine_upperLower N hA hB hδ hAc hBc hEq hR
```

The two ordered cases should be a one-line `exact` each — the hypotheses match
verbatim. Verify that claim before writing anything else; it is the cheapest
confirmation that this plan is sound.

### Item 5 — reroute the sine-theta glue (REQUIRED)

`SinTheta/Unbounded.lean:339` `generalizedSinTheta_unbounded_exact` and its
partner `generalizedSinTheta_unbounded` (both already `ℂ`-only). Reprove each
by delegating to the clean
`generalizedSinTheta_unbounded_{exact_,}of_genuineSpectrumGap`
(`SinTheta/GenuineAllGap.lean:39,73`) via Item 3/4. Everything else in these
proofs (`sinThetaBlock_mem_and_gauge_eq_directedSinThetaOperator`, the angle
identification) is already clean and must be preserved unchanged.

`GeneralSinThetaProblem.result`, `IsometricSinThetaProblem.result` and
`BoundedGeneralSinThetaProblem.result` (`SinTheta/Canonical.lean:52,190`,
`SinTheta/Specializations.lean:113`) should then become clean **with no edit at
all**, because they are thin wrappers. Confirm this; if one does not, report
why rather than patching around it.

### Item 6 — bounded specialization tail (CONDITIONAL)

`BoundedGeneralSinThetaProblem` reaches `realSpectrum` through
`boundedRealSpectrum` → `SpectrumInRealSet` → `IntervalExteriorGap`
(`SinTheta/SpectralBridge.lean:35,39,43`) and the converter
`intervalExteriorGap_to_unbounded` (`SinTheta/Specializations.lean`, which has
**no admission of its own** — it is polluted only by the definition).

After Item 1 this converter may become clean automatically. Check first. Only
if it does not, you additionally need these four, currently unproved
(`SinTheta/SpectralBridge.lean`):

| decl | line | content |
|---|---|---|
| `norm_sub_midpoint_le_of_spectrumIn_Icc` | 52 | `σ(A) ⊆ [β,α]` ⟹ `‖A − (β+α)/2‖ ≤ (α−β)/2` |
| `centered_isUnit_of_spectrumOutside` | 61 | exterior spectrum ⟹ centered operator boundedly invertible |
| `centeredIntervalExteriorWitness_of_gap` | 90 | witness packaging |
| `sylvester_mem_and_gauge_le_of_intervalExteriorGap` | 99 | bounded interval/exterior Sylvester estimate |

The first two are the real content (spectral radius = norm for self-adjoint
bounded operators; invertibility off the spectrum). **Prefer avoiding them** by
routing the bounded case through `ClosedOperator.ofBounded` into the already-
clean unbounded interval/exterior theorem.

## Explicitly OUT of scope — do not touch

- `Core/UnboundedSpectral.lean` (31 admissions: `selfAdjointSpectralProjection`,
  `spectralCutoff`, `boundedSpectralTruncation`, `filledSpectralTruncation`,
  `closedOperatorCayleyTransform`, …). This is **legacy infrastructure that the
  fixed chain must no longer depend on.** Proving it is a large independent
  research task and is *not* required. If your rerouting is correct, the whole
  file drops out of the sine-theta cone. That is the point.
- All continuation / Riccati / tangent-theta / spectral-repulsion work
  (`SinTheta/Continuation*.lean`, `TanTheta/`, `TanTwoTheta/`, `DirectRotation`,
  `Sharpness`, `DoubleAngle`).
- `Core/OperatorAngle.lean`, `Core/Forms.lean`, `Core/SpectralProjection.lean`.
- The concrete ideal-family instances in `Ideals/Rectangular.lean`
  (`hilbertSchmidt`, `traceClass`, `schatten`, `kyFan`, and compact-operator
  adjoint invariance). The theorem is parametric over an arbitrary
  `UnitaryInvariantIdealFamily`, and `KyFanDominantIdealFamily.operatorNorm`
  is an axiom-clean instance, so the result is already non-vacuous. Leave them.
- `Challenge/**/Conformance.lean` — immutable by repository policy.

## New declarations you are expected to create

None of these exist today:

1. `ClosedOperator.realResolventSet` — definition (Item 1)
2. `realSpectrum_eq_spectraSpectrum` — ℂ bridge (Item 2)
3. `GenuineUnboundedSylvesterGap.of_legacy` (interval/exterior case) (Item 3)
4. `davisKahan1970_sylvester_complex` — ℂ-specialized clean engine (Item 4)
5. possibly `boundedRealSpectrum_eq_foundation_realSpectrum` — compatibility
   between the closed-operator and bounded-operator spectrum notions (Item 1
   fallout)

Everything else is a *reproof of an existing statement*, not a new statement.
**Do not change any existing theorem statement.** If you believe a statement is
wrong, stop and report rather than editing it.

## Verification protocol — run all of it before reporting

```bash
cd ~/code/aiq-dkps-formalization
lake build                      # must be error-free
```

Then, in a scratch file:

```lean
import DavisKahan.Sources.DavisKahan1970.GeneralSinTheta
#print axioms ForMathlib.DavisKahan1970.sinTheta
#print axioms ForMathlib.DavisKahan1970.generalizedSinTheta
#print axioms ForMathlib.DavisKahan1970.generalizedSinTheta_boundedSpecialization
#print axioms ForMathlib.DavisKahan.Experimental.ExactSinTheta.davisKahan1970_sylvester_complex
```

All must print `[propext, Classical.choice, Quot.sound]` and nothing else.

Also confirm you have not regressed the already-clean genuine chain:

```lean
#print axioms ForMathlib.DavisKahan.Experimental.ExactSinTheta.GenuineIsometricSinThetaProblem.result
#print axioms ForMathlib.DavisKahan.Experimental.ExactSinTheta.directOrderedSylvesterEngine
```

And confirm no admissions were added:

```bash
git diff --stat
git diff | grep -nE '^\+.*\b(sorry|admit)\b'   # must be empty
```

Note that `lake build` only builds modules reachable from the library roots.
After finishing, check for unreachable modules you may have broken:

```bash
for f in $(find DavisKahan ForMathlib -name '*.lean'); do
  [ -f ".lake/build/lib/lean/${f%.lean}.olean" ] || echo "UNBUILT: $f"
done
```

`SinTheta/FullUnboundedAudit.lean` is intentionally unimported; compile it
directly with `lake env lean <path>`.

## Reporting standard

Report only what Lean accepted. For each item state: done / partially done /
blocked, with the exact error text if blocked. If you cannot discharge an item,
**leave the existing admission in place and say so** — do not replace a
`sorry`-backed proof with a differently-shaped `sorry`-backed proof, and do not
mark a wrapper "complete" because it compiles while its dependency cone is
still dirty. The `#print axioms` output is the only evidence that counts.

If Item 1's definition turns out to conflict with an existing downstream use in
a way that cannot be reconciled, stop and report the conflict rather than
weakening the definition — a wrong definition is worse than an absent one.
