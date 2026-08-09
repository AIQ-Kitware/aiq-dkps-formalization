# Comparator tool setup

`Challenge/` is the repository's comparator/regression surface for reusable
theorem statements isolated during the formalization. The directory names
`MathlibCandidate` and `MathlibPending` are historical; the direct Mathlib
submission track is closed and reusable library work now targets Tau Ceti through
`ForTauCeti`.

- `Challenge/**/Conformance.lean` states comparator challenges using intentional
  proof placeholders.
- `Challenge/**/Leaderboard.lean` imports the project implementation and exposes
  the corresponding solution theorem/axiom audit.
- `comparator/*.json` configures comparator runs.
- `formalization.yaml` records current comparator inventory and project metadata.

The comparator check needs external tools: `landrun`, `comparator`, and
`lean4export`.

## Do not fill challenge placeholders

The placeholders in `Challenge/**/Conformance.lean` are part of Comparator's
challenge/solution model, not repository proof debt. Implement or repair a theorem
in its ordinary library owner (`ForTauCeti`, `DavisKahan`, or a paper library) and
leave the conformance statement independent.

Comparator success checks statement matching, dependency boundaries, and kernel
acceptance under the configured rules. It does not certify paper-specific source
fidelity.

## Install tools

From the repository root:

```bash
bash scripts/install_comparator_tools.sh
```

The default tool locations are described by that script. Override its tool root
with `AIQ_COMPARATOR_TOOL_ROOT` when needed.

## Run checks

Run the configured default set with:

```bash
bash scripts/run_challenge_comparator.sh
```

Run one configuration with:

```bash
bash scripts/run_challenge_comparator.sh --config comparator/candidate-01-gram-rigidity.json
bash scripts/run_challenge_comparator.sh --config comparator/pending-davis-kahan-sin-theta.json
bash scripts/run_challenge_comparator.sh --config comparator/pending-davis-kahan-tan-two-theta.json
```

The old monolithic `pending-davis-kahan-part-iii.json` configuration was removed.
The Davis--Kahan endpoints now have dedicated comparator configurations for sine,
tangent, double-angle, projector-difference, Sylvester, and sharp forms. Do not
restore the aggregate config just because an older document names it.

The runner's `DEFAULT_CONFIGS` array and the `formalization.yaml` comparator list
are the current machine-readable inventory. `Challenge/README.md` explains the
retained challenge taxonomy.

Some `Leaderboard.lean` files are axiom-audit-only and intentionally have no
comparator configuration. The presence of a challenge directory therefore does
not imply a one-to-one config file.

## Development fallback

If real `landrun` cannot be used locally because of sandbox permissions, the runner
supports Comparator's fake-landrun development path:

```bash
bash scripts/run_challenge_comparator.sh --fake-landrun
```

A fake-landrun result exercises wiring but is not equivalent to the hardened
sandboxed comparator run.
