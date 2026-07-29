# Handoff: natural-input extensions after full sine-theta completion

Date: 2026-07-19
Base commit: `19e6d2fa5e5b886973128ea9ea9afa4cd9082b2f`

## Read this first

The immediate theorem goal is already achieved in the base commit.  The full
general 1970 sine-theta theorem is compiler-accepted for complex and real
Hilbert spaces, all three gap configurations, arbitrary source-facing
unitarily invariant ideal families, bounded specializations, and natural real
spectral-subspace inputs.  `FullPartIII` and the repository's explicit full
unbounded audit were rebuilt successfully by the Lean-enabled agent.

Do not reopen, retire, weaken, or re-prove that chain.  The optional files in
this overlay extend usability and verification while preserving the accepted
source facade unchanged.

The larger project goal remains a source-faithful formalization of the full
1970 Davis--Kahan paper.  Opportunistic work here should either improve the
completed sine-theta API or create reusable foundations for later theorem
families.

## What this overlay adds

### Compiler-pending Lean leaves

1. `Core/ReducingRestrictionExtras.lean`
   - reduction passes to the orthogonal complement;
   - bounded reduction induces the closed-operator reduction law;
   - the closed restriction agrees pointwise with bounded restriction.
2. `SinTheta/NaturalGenuineGeneralized.lean`
   - complex lower-frame natural spectral-subspace theorem, isolated from the
     accepted `NaturalGenuine.lean` file.
3. `SinTheta/NaturalReducing.lean`
   - scalar-generic reducing-subspace problem records;
   - explicit complex and real isometric and lower-frame result methods.
4. `SinTheta/NaturalBounded.lean`
   - bounded natural spectral-set forms for both scalar fields.
5. `SinTheta/NaturalGapConvenience.lean`
   - source-oriented names for all three gap constructors.
6. `SinTheta/NaturalTwoSubspace.lean`
   - sharp symmetric projector-gap combination from two directed estimates.
7. `SinTheta/NaturalExamples.lean`
   - compile-only operator-norm, Ky Fan, bounded, and concrete real examples.
8. `Sources/DavisKahan1970/GeneralSinThetaExtensions.lean`
   - optional aliases only; the accepted `GeneralSinTheta.lean` is untouched.
9. `Sources/DavisKahan1970/FullPartIIIExtensions.lean`
   - explicit build root for the extension layer.

### Verification and roadmap support

- exact dependency audit for the accepted and extension endpoints;
- public API manifest and consistency checker;
- stale and missing compiled-artifact detection;
- open-debt inventory grouped by full-paper roadmap role;
- mathematical audit of real spectral descent;
- upstream extraction plan for reducing restrictions.

## Corrections carried forward from the compiler repair

The prior static draft contained a real direction error in the orthogonal
projection decomposition.  Mathlib's theorem has the ambient vector on the
left and the projection sum on the right.  The new `NaturalReducing` proof uses
its symmetric orientation in both affected places.

A second tempting mathematical shortcut is explicitly rejected: averaging a
complex finite-rank approximant with its conjugate can double its rank, so it
cannot prove equality of approximation numbers at the same index.  The
accepted min--max route remains authoritative.

Additional standing rules from the repair pass:

- unresolved elaboration errors can conceal wrong theorem orientation;
- never classify all remaining failures as elaborational before the file
  compiles;
- qualify Spectra and complexification names when shadowing is possible;
- build vendored Spectra modules and import them rather than duplicating their
  declarations;
- the real route is finished and must not be retired;
- a green default build does not cover `FullPartIII` or the unbounded audit;
- stale compiled artifacts invalidate dependency conclusions.

## Compile order

First re-verify the accepted base:

```bash
lake build DavisKahan.Experimental.InfiniteDimensional.SinTheta.RealSpecializations
lake build DavisKahan.Sources.DavisKahan1970.GeneralSinTheta
lake build DavisKahan.Sources.DavisKahan1970.FullPartIII
lake env lean DavisKahan/Experimental/InfiniteDimensional/SinTheta/FullUnboundedAudit.lean
```

Then repair the optional leaves in this order:

```bash
lake build DavisKahan.Experimental.InfiniteDimensional.Core.ReducingRestrictionExtras
lake build DavisKahan.Experimental.InfiniteDimensional.SinTheta.NaturalGenuineGeneralized
lake build DavisKahan.Experimental.InfiniteDimensional.SinTheta.NaturalReducing
lake build DavisKahan.Experimental.InfiniteDimensional.SinTheta.NaturalBounded
lake build DavisKahan.Experimental.InfiniteDimensional.SinTheta.NaturalGapConvenience
lake build DavisKahan.Experimental.InfiniteDimensional.SinTheta.NaturalTwoSubspace
lake build DavisKahan.Experimental.InfiniteDimensional.SinTheta.NaturalExamples
lake build DavisKahan.Sources.DavisKahan1970.GeneralSinThetaExtensions
lake build DavisKahan.Sources.DavisKahan1970.FullPartIIIExtensions
lake env lean DavisKahan/Experimental/InfiniteDimensional/SinTheta/FullGeneralSinThetaExtensionsAudit.lean
```

Finally run:

```bash
python scripts/check_general_sin_theta_api.py
python scripts/audit_general_sin_theta.py --extensions
python scripts/inventory_davis_kahan_debt.py --write-json dev/davis-kahan-open-debt-inventory-2026-07-19.json
```

## Acceptance criteria

- every command above has zero Lean errors;
- every printed dependency list is exactly
  `[propext, Classical.choice, Quot.sound]`;
- the already accepted base endpoints remain unchanged and clean;
- no proof bypass, new assumption declaration, or weakened statement is added;
- `Core/UnboundedSpectral.lean` remains outside the trusted theorem dependency;
- only after these checks may the extension aliases be folded into the main
  `GeneralSinTheta.lean` facade.

## Likely compiler repair points

- `ReducesSubspace.orthogonal` simplification through double orthogonal
  complements;
- proof-dependent reduction witnesses in `reducingRestriction_ofBounded_apply`;
- definitional unfolding of `UnboundedSinThetaData` in the natural reducing
  wrappers;
- real versus complex directed sine operator names in lower-frame results;
- family-instance inference in the nontrivial Ky Fan example;
- theorem names and argument order for bounded restriction and spectral-set
  wrappers.

## Larger-paper follow-on

Once these extensions compile, do not send an agent blindly into the remaining
textual open-term count.  Use
`dev/davis-kahan-open-debt-inventory-2026-07-19.md` to triage theorem families.
The next likely high-value full-paper work is direct rotation and the tangent or
double-angle chain, followed by sharpness and equality content.  The legacy
unbounded cutoff facade is superseded and should remain quarantined.

## Status

This overlay was not compiled in the environment that produced it.  Treat all
new Lean leaves as complete mathematical proposals pending compiler repair.
