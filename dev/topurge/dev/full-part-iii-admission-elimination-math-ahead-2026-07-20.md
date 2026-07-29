# Full Part III admission-elimination math-ahead handoff

## Baseline and purpose

This batch is based on commit
`7463ca25c64a46c48411a2769b47714889974a97`, where all ordinary, production,
and explicit Experimental builds were green, the source Section 6 audit was
clean at 43 endpoints, and the structural checker was clean at 5/5.

The batch attacks the remaining full-Part-III proof debt without changing the
accepted Section 6 chain.  It is deliberately a **math-ahead** overlay: the
candidate bodies must be repaired against the pinned Lean, Mathlib, and vendored
Spectra APIs before any completion claim is made.

## What was recovered

A full Git-history search found that 174 of the 183 executable Davis--Kahan
admissions had earlier non-placeholder bodies in commit `2244e7c6bd7f`.
Every one of those declarations has an exact normalized signature match with
the current statement.  This batch restores only the bodies; it preserves the
newer imports, documentation, namespaces, declaration names, and statements.

The source commit was a work-in-progress commit and was not an accepted green
baseline.  Its bodies are mathematical proof plans expressed in Lean, not
compiler-certified implementations.  Many should repair locally; others refer
to old or proposed APIs and will need to be rewritten through the current
canonical abstractions.

The exact declaration inventory and signature hashes are recorded in:

- `dev/full-part-iii-math-ahead-restoration-manifest-2026-07-20.json`
- `dev/full-part-iii-math-ahead-restoration-manifest-2026-07-20.md`

Run `python3 scripts/check_full_part_iii_math_ahead.py` after every repair.  It
fails if any restored statement changes or if an unfinished proof term appears
outside the immutable challenge tree.

## The final nine obligations

The remaining nine terms were all in
`SinTheta/ContinuationRoadmap.lean`.  They were not used anywhere, and the file
was not imported by any module.  They duplicated a later, completed and much
stronger continuation development:

- `ContinuationContour` gives the finite-piece Mathlib path structure and the
  quantitative spectral-selection witness;
- `ContinuationTransport` gives the normalized operator-valued curve integral
  and quantitative norm control;
- `ContinuationSpectralIdentification` identifies the contour operator with
  the genuine measurable spectral projection;
- `ContinuationAssembly` and `ContinuationRotationChain` produce a finite mesh
  and compose local direct rotations;
- `ContinuationTheorem` packages the final unitary transport of selected
  spectral subspaces.

The obsolete file is therefore now an import-only implementation index.  This
is the only declaration removal in the batch.  It is conservative: all removed
names were unreferenced, never compiled, and strictly superseded by concrete
proof-carrying declarations.  Do not recreate a second contour representation.

## Repair order

Do not run concurrent Lake builds.  Use process exit status, not text matching,
as the success criterion.

Compile the changed modules in this dependency-oriented order:

1. `DavisKahan/Experimental/FiniteDimensional/Core/AngleOperators.lean`
2. `DavisKahan/Experimental/FiniteDimensional/Norms/Rectangular.lean`
3. `DavisKahan/Experimental/FiniteDimensional/Residual/AngleEmbeddings.lean`
4. `DavisKahan/Experimental/InfiniteDimensional/Core/AbstractSpectrum.lean`
5. `DavisKahan/Experimental/InfiniteDimensional/Core/OperatorAngle.lean`
6. `DavisKahan/Experimental/InfiniteDimensional/Core/SpectralProjection.lean`
7. `DavisKahan/Experimental/InfiniteDimensional/Ideals/Rectangular.lean`
8. `DavisKahan/Experimental/InfiniteDimensional/SinTheta/ContinuationRoadmap.lean`
9. `DavisKahan/Experimental/FiniteDimensional/DoubleAngle/SinTheta.lean`
10. `DavisKahan/Experimental/FiniteDimensional/Sharpness.lean`
11. `DavisKahan/Experimental/FiniteDimensional/TanTheta/GraphOperator.lean`
12. `DavisKahan/Experimental/InfiniteDimensional/Ideals/Symmetric.lean`
13. `DavisKahan/Experimental/InfiniteDimensional/Sylvester/Resolvent.lean`
14. `DavisKahan/Experimental/FiniteDimensional/DoubleAngle/TanTheta.lean`
15. `DavisKahan/Experimental/InfiniteDimensional/Sylvester/Basic.lean`
16. `DavisKahan/Experimental/FiniteDimensional/DirectRotation.lean`
17. `DavisKahan/Experimental/FiniteDimensional/Generalized.lean`
18. `DavisKahan/Experimental/InfiniteDimensional/SinTheta/General.lean`
19. `DavisKahan/Experimental/InfiniteDimensional/DoubleAngle.lean`
20. `DavisKahan/Experimental/InfiniteDimensional/DirectRotation.lean`
21. `DavisKahan/Experimental/InfiniteDimensional/SinTheta/Continuation.lean`
22. `DavisKahan/Experimental/InfiniteDimensional/Core/Unbounded.lean`
23. `DavisKahan/Experimental/InfiniteDimensional/OperatorBlocks/OffDiagonal.lean`
24. `DavisKahan/Experimental/InfiniteDimensional/Core/Forms.lean`
25. `DavisKahan/Experimental/InfiniteDimensional/Core/UnboundedSpectral.lean`
26. `DavisKahan/Experimental/InfiniteDimensional/Sharpness.lean`
27. `DavisKahan/Experimental/InfiniteDimensional/SinTheta/SpectralBridge.lean`
28. `DavisKahan/Experimental/InfiniteDimensional/Ideals/CompactAndSingular.lean`

This ordering is a starting point, not a claim that every imported prerequisite
is already green.  When one candidate uses a proposed helper that does not
exist, first search the current production and vendored Spectra trees for the
modern equivalent.  Add a new helper only when the concept is independently
useful and belongs in a canonical module.

## Proof-repair rules

- Preserve every signature guarded by the manifest checker.
- Never replace a source-general theorem with a finite or bounded specialization.
- Preserve alternate finite proofs when they have weaker dependencies or useful
  coordinate content.
- Reuse the completed production Section 6 and direct-Spectra paths instead of
  rebuilding them through the legacy truncation engine.
- Prefer current proof-carrying contour and spectral-calculus structures over
  the historical proposed `Contour` namespace.
- Keep the approximation-number and operator-ideal APIs rectangular and
  independently universe-polymorphic where currently stated.
- For a genuinely false statement, stop and provide a concrete counterexample
  and dependency analysis.  Do not silently change it, delete it, or weaken it.
- Do not remove a declaration merely because its first restored body is hard.
  Removal requires proof that it is neither paper-facing nor independently
  reusable and that no current or planned source endpoint needs it.

## Expected structural transition

The overlay intentionally removes every textual admission from executable
Davis--Kahan source.  Until the candidate files compile, the structural checker
will classify many Experimental modules as ready to promote even though they
are not yet compiler-certified.  Do not weaken or exempt the checker.

After the proofs compile:

1. run `python3 scripts/inventory_admission_closure.py`;
2. promote the now-complete modules into canonical production directories in
   dependency batches;
3. repoint source facades and regenerate aggregates;
4. leave `Experimental` only for genuinely unresolved work, if any remains;
5. require `python3 scripts/check_library_structure.py` to return CLEAN, 5/5.

## Acceptance sequence

After each module repair:

```bash
python3 scripts/check_full_part_iii_math_ahead.py
```

After all 28 changed modules compile:

```bash
python3 scripts/generate_all_aggregates.py --check
lake build
lake build DavisKahan.All
lake build DavisKahan.Experimental
python3 scripts/audit_full_paper_sine_theta.py
python3 scripts/check_full_part_iii_math_ahead.py
python3 scripts/check_library_structure.py
```

Also recompile the immutable recent proof targets:

```bash
lake env lean DavisKahan/Alternative/OperatorIdeal/HilbertSchmidt/ColumnExpansion.lean
lake env lean DavisKahan/Sources/DavisKahan1970/SineTheta/FiniteMultiplicity.lean
lake env lean DavisKahan/Sources/DavisKahan1970/Sylvester/PaperHilbertSchmidt.lean
```

The final report must distinguish:

- declarations repaired and compiler-accepted;
- declarations whose restored body was replaced by a different current-API
  proof;
- any statements shown false or malformed;
- any declarations removed, with the strict removal justification;
- source-paper endpoints newly closed;
- general reusable infrastructure newly closed;
- remaining Experimental modules and why they remain.

## Superseded completion contract

The original version of this handoff treated absence of unfinished proof tokens
as sufficient evidence that the restored batch was ready for compiler repair.
That was incorrect: most restored modules do not compile, and several bodies
refer to abstractions that never existed.

The authoritative continuation is now:

`dev/full-part-iii-staged-repair-plan-2026-07-20.md`

The default math-ahead checker is compiler-gated.  Do not use the earlier
static-only acceptance language or the original 28-module all-at-once repair
order.
