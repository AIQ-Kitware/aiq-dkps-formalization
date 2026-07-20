# Source-coordinate angle redesign overlay manifest

## Base

- Git commit: `90ef32fcc534de8204d7e71d793810f4142561c4`
- Source archive: `aiq-dkps-formalization-source-2026-07-20T174820-5-90ef32fcc534.tar.gz`
- Base working tree: clean, detached HEAD
- The compiler-clean rectangular Schatten and weak-majorization commits
  `a8d4ea3` and `90ef32f` are already present and are not replayed.

## Payload

- `DavisKahan/FiniteDimensional/Residual/AngleEmbedding.lean`
  - defines source-side cosine and sine Gram blocks;
  - defines the positive coordinate cosine `|C|`;
  - proves the Gram partition, square, kernel, injectivity, and singular-value bridges;
  - replaces the provisional double-angle cosine with
    `X (C⋆C - S⋆S)` and adds source/rectangular bridges;
  - adds the rectangular cosine/principal-cosine singular-value bridge.
- `DavisKahan/Experimental/FiniteDimensional/Residual/AngleEmbeddings.lean`
  - defines tangent as `S |C|⁺`;
  - defines double-angle sine as `2 S |C|`;
  - defines double-angle tangent using the source cosine pseudoinverse;
  - connects both totalized pseudoinverses to `inverseOnRange`.
- `DavisKahan/Experimental/FiniteDimensional/DoubleAngle/TanTheta.lean`
  - uses the source double-angle cosine;
  - removes the stale `FiniteDimensional.cosTwoThetaEmbedding` reference;
  - replaces a fictional inverse lemma with the canonical compatibility theorem.
- `dev/angle-coordinate-redesign-compiler-handoff-2026-07-20.md`
  - records the mathematical correction, likely elaboration seams, and sequential checks.

No change is made to
`DavisKahan/Experimental/InfiniteDimensional/Ideals/Rectangular.lean`.

## Mathematical correction

For `C = P_U X` and `S = P_{Uᗮ} X`, the principal-angle data lives in the
source Gram blocks. The correct positive cosine is
`|C| = (C⋆C)^(1/2)`. Consequently:

- tangent is `S |C|⁺`;
- double-angle sine is `2 S |C|`;
- double-angle cosine is `C⋆C - S⋆S` on source coordinates;
- double-angle tangent divides by that source cosine.

The former ambient formulas introduced an extra cosine factor even though
their types elaborated.

## Validation performed

Successful in the math-ahead environment:

- `python3 scripts/check_full_part_iii_math_ahead.py --static-only`:
  STATIC CLEAN, all 174 guarded signatures preserved;
- `python3 scripts/generate_all_aggregates.py --check`;
- `python3 scripts/inventory_davis_kahan_debt.py --json`:
  exactly 18 intentional Challenge occurrences;
- `git diff --check`;
- structural checker checks 1, 2, 4, and 5 remain clean, while check 3 has the
  same 116 inherited Experimental violations reported at the base commit;
- unified patch and ZIP independently applied to fresh base extractions;
- resulting payload files compared byte-for-byte;
- internal SHA-256 manifest verified.

Lean is not installed in the math-ahead environment. The new angle declarations
are complete candidate code, not compiler-certified code. The compiler handoff
lists the focused modules and likely elaboration seams. The already repaired
Schatten modules remain compiler-clean in the supplied base and were untouched.

## Deliberate boundary

The definitions now have the correct angle semantics. This overlay does not
assert the still-unproved simultaneous CS-decomposition results identifying the
singular values of the tangent and double-angle maps with scalar tangent
sequences. Those are separate mathematical theorems, not definitional facts.
