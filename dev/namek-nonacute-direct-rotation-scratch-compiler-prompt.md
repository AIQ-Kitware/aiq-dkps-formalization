Work only in `/home/joncrall/code/aiq-dkps-namek`.

Inspect the latest commit, then compile the additive Section 3 scratch target:

```bash
scripts/lake_build_report.py --fail-fast \
    DavisKahan.Experimental.Scratch.Section3.NonacuteExistence
```

The scratch file targets the hard converse in Davis--Kahan Proposition 3.2:
a paper direct rotation must map `U ⊓ Vᗮ` onto `Uᗮ ⊓ V`.  The intended proof is:

1. crossed-block skew-adjointness makes `T + T⋆` block diagonal relative to
   `U ⊕ Uᗮ`;
2. the two nonnegative compression hypotheses make `T + T⋆` positive;
3. for a crossed-defect vector, orthogonality makes its quadratic form zero;
4. positivity forces `(T + T⋆)x = 0`;
5. the adjoint intertwining relation gives the missing crossed membership.

Repair compiler/API issues narrowly in the scratch file.  Preserve all theorem
statements and this proof route unless an actual mathematical defect is found.
Do not modify the actively claimed production files
`MathAhead/HiddenFoundations/Section3Nonacute.lean`,
`Interop/Spectra/DirectRotation.lean`, or `Frontier/Section3.lean`.
Do not use `sorry`, `admit`, `native_decide`, new axioms, or weakened claims.

After the leaf target builds, run:

```bash
scripts/lake_build_report.py --fail-fast \
    DavisKahan.Experimental.Scratch.Section3.All
```

Report any theorem whose proof still depends on `sorryAx`; in particular,
verify that the scratch necessity direction does not depend on the two existing
production holes it is intended to replace.
