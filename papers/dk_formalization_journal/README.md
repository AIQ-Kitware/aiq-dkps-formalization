# Formalizing Davis--Kahan Perturbation Theory in Lean 4

**Current journal manuscript:** `paper.tex`. This is a formalization paper
covering the 1970 Davis--Kahan source, its Lean operator-theory prerequisites,
a source correction to Proposition 4.4, and one follow-on matching example.

For scientific scope and publication boundaries, read
[FORMALIZATION_PAPER_SCOPE.md](FORMALIZATION_PAPER_SCOPE.md).

The older mathematics-first manuscript, including the complete two-parameter
spectral-penalty theory, optimizer classifications, real matching, nuclear
endpoint, and infinite-dimensional extensions, is preserved as a buildable
source snapshot in [`../optimal_spectral_transport/`](../optimal_spectral_transport/).
Existing transport-oriented `.tex` files in this directory are historical
working sources and are **not included by `paper.tex`**. Work on that broader
mathematics belongs in the companion paper directory.

The retained 29 source targets consist of 28 formalized statements and one
formally refuted proposition. For traceable support see the source inventory,
`claims_to_evidence.md`, and the formalization appendices. Historical priority
of new transport results remains a separate literature question.

## Build

```bash
make -C papers/dk_formalization_journal paper
```

