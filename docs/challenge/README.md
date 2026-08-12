# AIQ challenge package

`Challenge/` is the repository's comparator, regression, and mathematical-
exhibition surface.  Challenges freeze recognizable theorem statements and
exercise dependency boundaries; they are not required to be proof-DAG leaves
and they do not encode a Mathlib submission queue.

The current layout is deliberately neutral:

* `Challenge/DavisKahan1970/` is the source-oriented Davis--Kahan 1970
  exhibition, including intentionally red exact-paper obligations.
* `Challenge/MathlibCandidate/` is retained as historical provenance for the
  three original candidate surfaces.
* Other challenge packages live directly under `Challenge/<Name>/`.  The old
  `Challenge/MathlibPending/` namespace has been removed.

Each comparator package conventionally pairs a `Conformance.lean`, which states
the challenge with intentional `sorry` placeholders, with a `Leaderboard.lean`,
which imports production code and exposes matching proofs plus axiom audits.
`comparator/*.json` names the modules and declarations to compare.  Some
leaderboard-only dependency audits intentionally have no comparator config.

The four DKPS-family paper libraries (`Acharyya2024`, `Acharyya2025`,
`DkpsQuench2026`, `Helm2025`) remain ordinary source-facing libraries rather than
comparator challenges.  Davis--Kahan 1970 has a dedicated challenge because the
repository uses it as an exhibition and an executable paper-faithfulness target.

## Running checks

Install comparator tools once:

```bash
bash scripts/install_comparator_tools.sh
```

Run all challenge families (continues through all configs, prints a summary):

```bash
bash scripts/run_challenge_comparator.sh
```

Run one family:

```bash
bash scripts/run_challenge_comparator.sh --config comparator/candidate-01-gram-rigidity.json
bash scripts/run_challenge_comparator.sh --config comparator/challenge-rank-factorization.json
```

If real `landrun` is unavailable while debugging, use `--fake-landrun` (not the
hardened sandboxed check). A real result should use real `landrun`.
