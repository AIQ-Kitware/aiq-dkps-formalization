# Davis--Kahan 1970 completion standard

This path is kept because source modules and engineering notes cite it, but the old
rolling completion diary has been removed. It mixed durable scope rules with
week-by-week status and repeatedly went stale.

## Durable completion standard

The target is the scope actually stated by Davis and Kahan (1970), not merely a
finite-dimensional surrogate. Claims should therefore distinguish:

- finite-dimensional specializations;
- bounded Hilbert-space results;
- source unitary-invariant-norm scope;
- unbounded self-adjoint extensions with explicit domain conditions;
- exact source-numbered results and source-level counterexamples.

A paper result is complete only when its source-facing statement is represented by
compiled, admission-free Lean at the intended scope, or when the source claim has
been classified honestly (for example, Proposition 4.4 is refuted rather than
proved).

## Live status

Do not maintain a second prose status ledger here. The current authorities are:

- `dev/davis-kahan-1970-full-source-census.json` -- source-by-source status and
  verification;
- `dev/davis-kahan-1970-full-source-census.md` -- generated readable census;
- `dev/davis-kahan-1970-formalization-result-inventory.md` -- the 29-result
  completion denominator and its status;
- `AGENTS.md` -- current project policy and ownership rules;
- `DavisKahan/Sources/DavisKahan1970/README.md` -- publication-facing overview.

Validate the maintained census with:

```bash
python3 scripts/check_davis_kahan_1970_source_census.py
aiq-lean census render dev/davis-kahan-1970-full-source-census.json \
    -o dev/davis-kahan-1970-full-source-census.md --check
```

When Lean is available, use the repository's compile-backed census probes rather
than copying their output into this document.

## Historical detail

The former 1,000-line rolling roadmap remains available in Git history. Use it only
for provenance of an old design decision; do not use an old status paragraph to
infer what remains open today.
