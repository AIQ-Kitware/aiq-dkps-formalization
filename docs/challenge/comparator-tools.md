# Comparator tool setup

`Challenge/` is the repository's comparator/regression surface for reusable
theorem statements isolated during the formalization. The direct Mathlib submission track is closed and reusable library work now
targets Tau Ceti through `ForTauCeti`.  The obsolete `MathlibPending` directory
has been removed; neutral challenges live directly under `Challenge/<Name>/`.
`MathlibCandidate` remains only as historical provenance for the original three
candidate surfaces.

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
bash scripts/run_challenge_comparator.sh --config comparator/davis-kahan-1970.json
```

The Davis--Kahan 1970 source exhibition is consolidated in
`comparator/davis-kahan-1970.json`; the old split `pending-davis-kahan-{sharp,
sin-theta,sin-two-theta,tan-theta,tan-two-theta,projector-difference}.json` files
were retired.  The later Sylvester `pi/2` infrastructure remains a separate
historical comparator because it is not a theorem of the 1970 paper.

The consolidated Davis--Kahan config is **intentionally red** while the literal
directed-residual and ambient Section 2 `tan 2Theta` endpoints are not both
available with exactly the printed hypotheses.  It is therefore not part of the
runner's default green set.  Run it explicitly when auditing paper-faithful
completion; failures on the two `*_exactPaper` tan-2Theta targets are currently
expected.

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
