# Comparator tool setup

This repository includes a challenge package for the AI-authored Mathlib-candidate
lemmas:

- `Challenge/*/Conformance.lean` imports only Mathlib and states the challenge
  claims with `sorry`.
- `Challenge/*/Leaderboard.lean` imports this project and fills those claims.
- `comparator/*.json` configures comparator runs.
- `formalization.yaml` records provenance and AI usage notes.

The comparator check needs external tools: `landrun`, `comparator`, and
`lean4export`. The working setup used `landrun` from the `main` branch rather
than the latest released tag.

## Do not fill challenge placeholders

The proof placeholders in `Challenge/**/Conformance.lean` are intentional. They
are the trusted challenge statements that Comparator compares against the
project implementation imported by `Leaderboard.lean`. Filling them locally
would destroy the separation between statement and solution and would not
advance the formalization. The official Comparator model explicitly permits a
challenge theorem to contain a placeholder while requiring the solution theorem
to match its statement and use only the configured permitted dependencies:
<https://github.com/leanprover/comparator>.

When a project theorem is unfinished, work in `ForMathlib/`, the paper namespace,
or another ordinary library module. Never repair a red dependency audit by
editing the corresponding `Conformance.lean`.

## Install tools

From the repository root:

```bash
bash scripts/install_comparator_tools.sh
```

By default this uses:

```text
~/code/lean-tools/comparator
$(go env GOPATH)/bin/landrun
```

Override the tool root if desired:

```bash
AIQ_COMPARATOR_TOOL_ROOT=/tmp/lean-tools bash scripts/install_comparator_tools.sh
```

## Run checks

From the repository root:

```bash
bash scripts/run_challenge_comparator.sh
```

This performs:

```bash
lake env lean Challenge/MathlibCandidate/GramRigidity/Conformance.lean
lake env lean Challenge/MathlibCandidate/GramRigidity/Leaderboard.lean
lake build Challenge.MathlibCandidate.GramRigidity.Leaderboard
lake env comparator comparator/candidate-01-gram-rigidity.json
```

using explicit `COMPARATOR_LANDRUN` and `COMPARATOR_LEAN4EXPORT` paths.

The advertising-level Davis--Kahan configs can also be run individually:

```bash
bash scripts/run_challenge_comparator.sh --config comparator/pending-davis-kahan-sharp.json
bash scripts/run_challenge_comparator.sh --config comparator/pending-davis-kahan-part-iii.json
bash scripts/run_challenge_comparator.sh --config comparator/pending-davis-1963-rotation.json
bash scripts/run_challenge_comparator.sh --config comparator/pending-yu-wang-samworth.json
```

`Challenge/MathlibPending/RectangularFanDominance/Leaderboard.lean` is an
axiom-audit-only flagship until its definitions are separated from their
implementation module; it intentionally has no comparator config yet.

## Development fallback

If real `landrun` fails locally with a sandbox permission error, the wiring can
be checked with comparator's fake landrun wrapper:

```bash
bash scripts/run_challenge_comparator.sh --fake-landrun
```

A fake-landrun pass is useful for development, but it is not the hardened
sandboxed check. The real check should end with:

```text
Lean default kernel accepts the solution
Your solution is okay!
```


## Current challenge layout

The challenge files now live under `Challenge/` rather than at repository root.
The runner reads the module names from each comparator JSON file and derives the
corresponding paths automatically.

Default configs run by `scripts/run_challenge_comparator.sh`:

* `comparator/candidate-01-gram-rigidity.json`
* `comparator/candidate-02-courant-fischer-weyl.json`
* `comparator/candidate-03-davis-kahan.json`
* `comparator/pending-davis-kahan-sharp.json`
* `comparator/pending-davis-kahan-part-iii.json`
* `comparator/pending-davis-1963-rotation.json`
* `comparator/pending-yu-wang-samworth.json`
* `comparator/pending-*.json` (Berge, RankFactorization, RankPsdRealization,
  RestrictCoverMeasurable, SampleMeanMSE, NearIsometry, CfcMeasurable,
  MatrixConcentration, ProbabilityQoL, TendstoInMeasure)

See `Challenge/README.md` for the manifest. SpectralFunctionMeasurable and
RectangularFanDominance are axiom-audit leaderboards only (no comparator
config). The four DKPS papers are documented, not comparator challenges.
