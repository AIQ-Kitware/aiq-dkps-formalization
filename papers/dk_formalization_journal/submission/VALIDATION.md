# Validation and reproduction — 23 October 2026

## Snapshot and original result inventory

This manuscript revision uses the source archive for commit
`5b9c81c4739607f74547f3c55813ebbfc4f00696` (23 October 2026).
The original 29 Davis--Kahan source targets remain 28 proved at reviewed scope
and one refuted as printed (Proposition 4.4). This inventory is independent
of subsequently added correction and optimization theorems.

## Lean development

The project owner previously reported successful compilation (3,477 jobs) of
`SmallAngleCounterexample`, `Section4SmallAngle`, and the corresponding audit
module on 23 October. That run also recorded the standard dependencies
`propext`, `Classical.choice`, and `Quot.sound` for its inspected declarations.

In the later source snapshot, the agent has completed the additional proof
modules. The declarations themselves were inspected for this manuscript
revision and the owner reports that the agent completed the Lean proofs.
Their contents support the following scope:

| Module | Proved mathematical content |
|---|---|
| `ProjectionDisplacement` | UI-seminorm projection lower bound, real/complex and without acuteness. |
| `TraceRatio` | Exact direct/competitor trace ratio on the real family. |
| `TraceOptimality` | Global real four-dimensional trace-norm minimum. |
| `SharpDisplacement` | Sharp `cos(alpha/2)` direct-rotation bound, uniform optimality, `2/sqrt(3)` and `sqrt(2)` factors. |
| `ComplexTraceOptimality` | Attained complex two-plane trace minimum, including right angles. |
| `ComplexTraceAssembly` | Finite orthogonal sums of the complex phase-plane models. |
| `ComplexTraceFiniteModel` | Finite specified principal-plane models, fixed summands, and ambient isometric transport. |

The `ComplexTraceFiniteModel` results do **not** automatically produce a
principal-plane decomposition for every arbitrary pair of complex subspaces.
The all-pairs trace-minimum theorem is excluded from the checked-only paper;
its conventional proof is retained solely in the optional red research box.

To reproduce the quantitative extensions, from the repository root run:

```bash
lake exe cache get
lake build \
  DavisKahan.FiniteDimensional.DirectRotation.SmallAngleCounterexample \
  DavisKahan.FiniteDimensional.DirectRotation.ProjectionDisplacement \
  DavisKahan.FiniteDimensional.DirectRotation.TraceRatio \
  DavisKahan.FiniteDimensional.DirectRotation.TraceOptimality \
  DavisKahan.FiniteDimensional.DirectRotation.SharpDisplacement \
  DavisKahan.FiniteDimensional.DirectRotation.ComplexTraceOptimality \
  DavisKahan.FiniteDimensional.DirectRotation.ComplexTraceAssembly \
  DavisKahan.FiniteDimensional.DirectRotation.ComplexTraceFiniteModel \
  DavisKahan.Sources.DavisKahan1970.Section4SmallAngle
```

These additional modules are not necessarily imported by the ordinary
`lake build` aggregate. The build command here explicitly names them;
the printed-source 29-result inventory is unaffected. No extra
`#print axioms` inventory or duplicate proof-checker is needed for routine
proof development.

## Manuscript compilation

The default `paper.tex` omits the only unformalized all-pairs complex
proposition. `\includeUnformalizedComplexTracetrue` includes it in an
explicitly red, breakable working-draft frame; false is the default.
Both variants should be generated for editorial review, but only the
checked-only variant is intended as the manuscript itself.

Build from the repository root with
`make -C papers/dk_formalization_journal paper`.
The sandbox manuscript build uses TeX Live and `bibtex8` in place of a
missing `bibtex` executable; the LaTeX build tests do not rerun Lean.

## Scholarly priority

The cited primary literature establishes the prior complex phase mechanism,
Q-norm minimality and related Schatten failures, the later repetition of the
short-angle claim, and recognition of general trace-norm nonminimality.
It does not establish first-publication priority for the exact real short-angle
correction or for the sharp uniform comparison; the paper claims neither.
The page-keyed detail is in `PROPOSITION_4_4_LITERATURE_MAP.md`.
