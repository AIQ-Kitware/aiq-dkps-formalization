# Weak-agent completion guide: full unbounded sine-theta

## Exact completion target

The target is the complex Hilbert-space, domain-aware, genuine-spectrum,
all-gap, arbitrary unitary-invariant ideal-gauge Davis--Kahan sine-theta
result. The final source-shaped endpoints are:

- `GenuineGeneralSinThetaProblem.result`
- `GenuineIsometricSinThetaProblem.result`

A green build is not enough by itself. The trusted-dependency audit in
`SinTheta/FullUnboundedAudit.lean` must show no `sorryAx` dependency for these
capstones.

This guide is deliberately independent of the Section 8 continuation,
selected-graph, Riccati, quarter-turn, and spectral-repulsion stream. Do not
edit Agent 4 files while following it.

## Current proof graph

Already complete and intended to remain unchanged:

1. Domain-aware closed-operator and residual-block packaging.
2. Lower-frame normalization and exact directed-angle identification.
3. Genuine interval/exterior localization and both interval/exterior
   Sylvester orientations.
4. Genuine half-line spectrum containment to form semibounds:
   - `semiboundedBelow_of_spectrum_subset_Ici`
   - `semiboundedAbove_of_spectrum_subset_Iic`
5. Final genuine all-gap Sylvester and sine-theta assembly.

The only analytic replacement point is:

- `canonicalOrderedSylvesterEngine`

It has exactly two fields:

- `OrderedSylvesterEngine.lowerUpper`
- `OrderedSylvesterEngine.upperLower`

The current value is a compatibility implementation through the legacy
cutoff development. The entire completion can be made trusted-dependency clean
by constructing a direct Spectra implementation and changing the canonical
value to that implementation.

## Do not broaden the task

Do not repair every declaration in `Core/UnboundedSpectral.lean`. Most of that
file is outside the dependency-minimal route. Do not work on continuation,
Riccati, tangent, double-angle, public umbrellas, source facades, or aggregate
modules.

Do not import the root `Spectra` module. Use the repository's vendored
`vendor/Spectra` modules and import the narrowest files needed.

## Phase 0: establish the baseline

Run:

```bash
lake build \
  DavisKahan.SpectralTheory.OrderedHalfLine \
  DavisKahan.Experimental.InfiniteDimensional.Sylvester.CutoffInterface \
  DavisKahan.Experimental.InfiniteDimensional.Sylvester.GenuineOrderedEngine \
  DavisKahan.Experimental.InfiniteDimensional.Sylvester.GenuineAllGap \
  DavisKahan.Experimental.InfiniteDimensional.SinTheta.GenuineAllGap

lake env lean \
  DavisKahan/Experimental/InfiniteDimensional/SinTheta/FullUnboundedAudit.lean
```

Record the exact trusted-dependency output before changing anything.

## Phase 1: direct Spectra cutoff interface

Create a new leaf, preferably:

```text
DavisKahan/Experimental/InfiniteDimensional/Sylvester/SpectraCutoffInterface.lean
```

Construct:

```lean
noncomputable def spectraSpectralCutoffInterface
    (A : ClosedOperator ...) (hA : A.IsSelfAdjoint) :
    SpectralCutoffInterface A hA
```

Use the vendored Spectra group for the self-adjoint partial operator:

```lean
Spectra.YosidaHille.genToGroup hA
```

and the symmetric band projection:

```lean
Spectra.QuantumMechanics.SpectralTheory.spectralProjection
  (Spectra.YosidaHille.genToGroup hA)
  (Set.Icc (-τ) τ)
  measurableSet_Icc
```

Map each interface field to these vendored results:

| Interface field | Primary vendored theorem |
| --- | --- |
| idempotence | `spectralProjection_inter` with the same interval |
| symmetry | `spectralProjection_adjoint` |
| range in domain | `spectralProjection_mem_generatorDomain` |
| domain commutation | `generator_spectralProjection_comm` |
| strong convergence | `tendsto_spectralProjection_Icc_univ` plus a real-parameter cofinality bridge |

Use `generator_genToGroup hA` to transport the domain and operator action back
to the DK closed-operator wrapper. Prefer explicit `change` and `calc` blocks;
do not expect proof terms with different domain witnesses to rewrite directly.

The real-parameter strong limit is the one nontrivial packaging point because
the strongest vendored theorem is indexed by natural numbers. Prove a small
cofinality lemma rather than reproving spectral convergence.

### Phase 1 compile gate

```bash
lake build \
  DavisKahan.Experimental.InfiniteDimensional.Sylvester.SpectraCutoffInterface
```

Do not continue until this target is green.

## Phase 2: direct bounded truncation interface

In the same leaf or a second leaf, construct:

```lean
noncomputable def spectraBoundedTruncationInterface
    (A : ClosedOperator ...) (hA : A.IsSelfAdjoint) :
    BoundedTruncationInterface A hA
      (spectraSpectralCutoffInterface A hA)
```

Use the bounded measurable symbol

```lean
fun λ : ℝ => (λ : ℂ) *
  Set.indicator (Set.Icc (-τ) τ) (fun _ => (1 : ℂ)) λ
```

through `spectralCalculus`. The key vendored results are:

- `id_indicator_measurable`
- `id_indicator_bdd`
- `generator_spectralProjection`
- `generator_spectralProjection_comm`
- `spectralCalculus_mul`
- `spectralCalculus_adjoint`
- `weak_first_moment`
- `tendsto_spectralProjection_Icc_univ`

Suggested proof order:

1. Define the truncation.
2. Prove symmetry from the real-valued symbol.
3. Prove equality on the cutoff range using
   `generator_spectralProjection`.
4. Prove commutation with the cutoff by indicator multiplication.
5. Derive lower and upper bounds by applying the existing form semibound to the
   cutoff vector; avoid a second integration proof.
6. Prove convergence on the domain by rewriting the truncation as the cutoff
   applied to `A x`, then use strong cutoff convergence.

### Phase 2 compile gate

Build only the direct interface leaf. Then build
`GenuineCutoffInterface` to verify that no import cycle was introduced.

## Phase 2.5: bounded Theorem 5.1 trusted seam

The finite Ky Fan proof in `Sylvester/Unbounded.lean` currently calls
`sylvester_mem_and_gauge_le_of_bound_inverse` and its swapped orientation.
Those declarations are not yet trusted-dependency clean.  Complete a new
Neumann-series proof in a separate leaf before using the finite cutoff result
in the canonical engine.  Do not hide this dependency by calling the legacy
Theorem 5.1 declarations.

The clean bounded leaf should export:

```text
boundedSylvester_mem_and_gauge_le_of_bound_inverse
boundedSylvester_mem_and_gauge_le_of_bound_inverse_swapped
```

Compile and audit those two declarations independently before continuing.

## Phase 3: generic ordered Ky Fan engine

The interface mechanics are split into an initial compile-local leaf:

```text
DavisKahan/Experimental/InfiniteDimensional/Sylvester/GenuineOrderedFromCutoffs.lean
```

It contains the filled truncation, global form bounds, double-cutoff equation,
and left/right strong-cutoff Ky Fan limit steps.  Keep the bounded finite
estimate separate so errors cannot mix spectral-domain transport with the
Neumann-series ideal argument.


Create:

```text
DavisKahan/Experimental/InfiniteDimensional/Sylvester/GenuineOrderedFromCutoffs.lean
```

Prove a constructor with this conceptual shape:

```lean
noncomputable def genuineOrderedSylvesterEngine_of_interfaces
    (cutoff : ∀ A hA, SpectralCutoffInterface A hA)
    (truncation : ∀ A hA,
      BoundedTruncationInterface A hA (cutoff A hA)) :
    OrderedSylvesterEngine
```

Do not invent a new analytic argument. Port the already accepted proof in
`Sylvester/Unbounded.lean` in the following exact order:

1. Generalize `filledSpectralTruncation` to the supplied interface.
2. Generalize the Pythagorean cutoff identities.
3. Generalize the double-cutoff Sylvester equation.
4. Generalize right and left strong-cutoff Ky Fan convergence.
5. Generalize the finite double-cutoff estimate.
6. Apply `mem_and_scaled_gauge_le_of_all_scaled_kyFan_le`.
7. Obtain the reversed orientation by the mirrored finite-cutoff proof already
   present in the source file.

Copy one theorem at a time and compile after each theorem. Never copy the whole
section and debug it as one unit.

### Suggested theorem seams

Use these names so later agents can search them directly:

```text
interfaceFilledTruncation
interfaceFilledTruncation_isSymmetric
interfaceFilledTruncation_lowerBound
interfaceFilledTruncation_upperBound
interfaceDoubleCutoff_sylvester_equation
kyFan_le_of_interfaceRightCutoff_le
kyFan_le_of_interfaceLeftCutoff_le
kyFan_ordered_le_of_interfaces
kyFan_ordered_swapped_le_of_interfaces
genuineOrderedSylvesterEngine_of_interfaces
```

Each theorem should have one responsibility and one local compile target.

## Phase 4: switch the canonical engine

Define:

```lean
noncomputable def spectraGenuineOrderedSylvesterEngine :
    OrderedSylvesterEngine :=
  genuineOrderedSylvesterEngine_of_interfaces
    spectraSpectralCutoffInterface
    spectraBoundedTruncationInterface
```

Then change only:

```lean
canonicalOrderedSylvesterEngine
```

to point at `spectraGenuineOrderedSylvesterEngine`.

Do not edit final sine-theta theorem statements.

## Phase 5: final gates

Run the checker:

```bash
python3 scripts/check_full_unbounded_sin_theta.py --build
```

Then manually inspect:

```bash
lake env lean \
  DavisKahan/Experimental/InfiniteDimensional/SinTheta/FullUnboundedAudit.lean
```

Required result:

- all listed targets build;
- neither final problem result reports `sorryAx`;
- no dependency on external/system Spectra;
- no Agent 4 file changed;
- no shared aggregate or public source facade changed.

## Error-recovery rules for a weak agent

1. Treat every failed overlay as reverted and rebuild the complete changed file
   from the newest archive.
2. Work on one declaration at a time.
3. Read the exact vendored theorem signature before writing a proof.
4. When domain witnesses differ, prove equality of underlying vectors and use
   `Subtype.ext`; do not rewrite proof terms.
5. When a `spectralProjection` expression fails to match, unfold only the
   local definition and align `genToGroup hA` explicitly.
6. When a calculation involving `id - P` becomes unstable, apply the operator
   equality to a vector first and use `map_sub` explicitly.
7. Do not replace genuine spectra by eigenvalue assumptions.
8. Do not weaken arbitrary ideal-gauge scope to operator norm.
9. Do not bypass the two-unbounded case by assuming one block is bounded.
10. Do not claim completion until the final trusted-dependency audit is clean.

## Ready-to-paste handoff prompt

You are responsible only for the full unbounded genuine-spectrum all-gap
Davis--Kahan sine-theta completion. Read
`dev/full-unbounded-sin-theta/README.md` first. Do not touch continuation,
selected-graph, Riccati, tangent, Section 8, public facades, or aggregate files.
Use only vendored dependencies. Work declaration-by-declaration through phases
1--5, compile after every declaration, and report the exact first compiler
failure. The final gate is a clean trusted-dependency report for
`GenuineGeneralSinThetaProblem.result` and
`GenuineIsometricSinThetaProblem.result`.
