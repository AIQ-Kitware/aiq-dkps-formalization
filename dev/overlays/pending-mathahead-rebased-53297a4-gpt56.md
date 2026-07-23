# Pending mathematics-ahead work rebased on `53297a4`

This package rebases the three still-pending mathematics-ahead campaigns onto
the compiler agent's repaired source archive at commit `53297a4`.

## Deliberately excluded

The following are already in the base and are not repeated:

- the 72-node frontier scaffold (`bdcd462` and subsequent repairs);
- the operator-semigroup Sylvester overlay (`5e4a647`);
- the compiler repairs through `53297a4`;
- the compiled scalar Haagerup--Zsidó kernel and exact `pi/(2d)` mass;
- the compiled bounded exponential group laws and public Sylvester API.

No existing production or compiler-repaired source file is modified.  All Lean
changes are additive under `DavisKahan/Experimental/MathAhead/`.

## Included campaigns

### Lane 1: geometry and Section 3

Aggregate:

```text
DavisKahan.Experimental.MathAhead.GeometryAll
```

Includes the generic Halmos restrictions, corrected Lemma 6.3 leakage theorem,
polar-factor infrastructure, nonacute direct rotations, operator-level
classification, and explicit spectral-multiplicity interfaces.

### Lane 2: Sylvester finite-step and ideals

Aggregate:

```text
DavisKahan.Experimental.MathAhead.SylvesterAll
```

Includes the Spectra-backed self-adjoint Borel calculus bridge, finite spectral
steps, orthogonal-idempotent exponentials, finite block Fourier reconstruction,
Ky Fan Bochner estimates, real descent, Hilbert--Schmidt packaging, and the
Schatten approximation-number interface.

The pivotal discovery is that vendored Spectra already provides the required
bounded real-line calculus as `Spectra.QuantumMechanics.SpectralTheory.spectralCalculus`
for `genToGroup` of a self-adjoint generator.  Do not rebuild a scalar PVM
integral from first principles before checking this bridge.

### Lane 3: Section 8 circle continuation

Aggregate:

```text
DavisKahan.Experimental.MathAhead.ContinuationAll
```

This reuses the repository's proof-carrying contour/Riesz layer and only adds a
circle specialization.  It does not revive the removed fictional `Contour.*`
API.  Its consumer chain remains affected by the independent
`SinTheta/General.lean` migration breakage.

### Lane 4: Section 9 free beam

Aggregate:

```text
DavisKahan.Experimental.MathAhead.Section9All
```

Includes the classical mode calculation, boundary determinant,
`cos beta * cosh beta = 1` characteristic equation, exact `4.73^4 > 500`, and
explicit interfaces for root localization and the interval Sobolev/Green
identity/self-adjoint realization.

## Compile order

```bash
lake env lean DavisKahan/Experimental/MathAhead/Section3Elementary.lean
lake env lean DavisKahan/Experimental/MathAhead/Lemma63.lean
lake env lean DavisKahan/Experimental/MathAhead/GeometryAll.lean

lake env lean DavisKahan/Experimental/MathAhead/Sylvester/SelfAdjointBorelCalculus.lean
lake env lean DavisKahan/Experimental/MathAhead/Sylvester/FiniteStepCalculus.lean
lake env lean DavisKahan/Experimental/MathAhead/Sylvester/OrthogonalIdempotentExp.lean
lake env lean DavisKahan/Experimental/MathAhead/Sylvester/FiniteBlockReconstruction.lean
lake env lean DavisKahan/Experimental/MathAhead/SylvesterAll.lean

lake env lean DavisKahan/Experimental/MathAhead/Section9All.lean
lake env lean DavisKahan/Experimental/MathAhead/ContinuationAll.lean
```

Compile `DavisKahan/Experimental/MathAhead/All.lean` only after the four lanes
are individually understood.

## Integration points into the repaired Sylvester file

The main candidate replacements are recorded in
`dev/davis-kahan-borel-mathahead-candidates.json`:

- `FiniteSpectralStep.sum_projection_eq_one` from the PVM finite-union/support layer;
- `FiniteSpectralStep.norm_operator_sub_le` from the Borel spectral sup bound;
- `unitaryGroup_finiteSpectralStep` from coefficientwise exponential;
- `finiteSpectralStep_reconstruction` from the blockwise Fourier theorem.

The compiler agent should copy or refactor the candidate proofs into the exact
existing declarations in `FourierSemigroup.lean`; it should not import an
experimental candidate from the production-facing file merely to close an
obligation.

## Semantic constraints

- General two-sided spectral separation has constant `pi/2`, not `1`.
- Ordered separation retains constant `1`.
- Lemma 6.3 assumes `K * P = Q * K * P`, not `K * P = Q * K`.
- A measurable Borel symbol must also be bounded on the actual spectrum before
  it defines a bounded operator.
- Proposition 4.4 is false and must not be restored.
- Interface records in the hidden-foundation campaign are roadmap boundaries,
  not proofs of the represented analytic theorem.
