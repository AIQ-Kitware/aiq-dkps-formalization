# Rectangular Schatten rebased overlay manifest

## Base

- Git commit: `48b436e512f535cb360958945b52a8aca3c76b20`
- Source archive: `aiq-dkps-formalization-source-2026-07-20T171816-5-48b436e512f5.tar.gz`
- Base working tree: clean, detached HEAD

## Payload

- `ForMathlib/Analysis/Normed/FiniteLpGauge.lean`
  - finite prefix sums and canonical weak majorization;
  - finite symmetric gauges and T-transform monotonicity;
  - real lp and infinity gauges, Minkowski, and zero padding.
- `ForMathlib/Analysis/InnerProductSpace/SchattenNorm.lean`
  - minimum-dimension singular-value vectors;
  - public rectangular Ky Fan subadditivity;
  - singular-value weak majorization for sums;
  - rectangular Schatten norms and S1, S2, infinity, adjoint, unitary, and ideal bridges.
- `DavisKahan/Experimental/FiniteDimensional/Norms/Rectangular.lean`
  - guarded compatibility wrapper preserving `ofSquareFamily`, `schatten`, and `mem_schatten`.
- `ForMathlib.lean`
  - roots the two new production modules while retaining the Stage 1 roots.
- `dev/rectangular-schatten-compiler-handoff-2026-07-20.md`
  - compiler order, likely API seams, validation commands, and response to the Stage 1 report.

## Rebase notes

The Stage 1 compiler commit changed no payload source file. The root aggregate
was merged rather than replaced, preserving imports of both
`SelfAdjointFunctionalCalculus` and `MoorePenroseInverse`.

The handoff accepts the functional-calculus, Moore-Penrose, and equal-rank
principal-angle repairs. It separately flags the current trial-coordinate
single- and double-angle embedding definitions as type-correct but not yet
singular-value-correct; they are outside this finite Schatten compiler pass.

## Validation performed

- static Part III contract: clean, all 174 guarded signatures preserved;
- aggregate generation check: clean;
- debt inventory: exactly 18 intentional Challenge occurrences;
- unified diff whitespace check: clean;
- ZIP and patch application independently verified against fresh base
  extractions;
- resulting payload files compared byte-for-byte;
- internal SHA-256 manifest verified.

Lean compilation is intentionally delegated to the compiler agent because the
math-ahead environment has no Lean executable or build cache.
