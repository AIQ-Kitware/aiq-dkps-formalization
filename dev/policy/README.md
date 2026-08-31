# `dev/policy/` — what this repository decides

Every file here is **data**. The mechanisms that read them are the installed
`aiq-lean-formalization-tools` package (developed in
`submodules/aiq-lean-formalization-tools`, consumed as an installed package):

```bash
python3 -m pip install -e submodules/aiq-lean-formalization-tools
aiq-lean gates run --config dev/policy/gate-suite.yaml --fast
```

That split is the point. Before 2026-08-30 each of these rules lived inside its
own `scripts/check_*.py`, so the architecture decision and the parser that
enforced it were the same file, and the parser was rewritten once per checker.

| File | Read by | Holds |
|---|---|---|
| `gate-suite.yaml` | `aiq-lean gates list\|run` | which gates exist, which are slow, which scripts are still discovered |
| `import-layers.yaml` | `aiq-lean imports check` | the library layering firewall and its ratcheting exceptions |
| `namespaces.yaml` | `aiq-lean namespaces check` | which namespaces `ForTauCeti` may declare into, and the donor namespace nothing may use |
| `ratchet.yaml` | `aiq-lean ratchet check` | `@[expose]` counts and why they may not simply be raised |
| `docstring-baseline.json` | `aiq-lean source docstrings --baseline` | undocumented public declarations accepted today |
| `private-shadow-baseline.json` | `aiq-lean source private-shadows --baseline` | accepted private-name wrappers, one reason each |
| `aggregate-header.txt` | `aiq-lean source aggregates --header-file` | the copyright header generated aggregates carry |

One policy lives elsewhere, next to the data it governs: the `policy` /
`reconstruction` blocks inside `prose/distilled_literature/source_manifest.json`.

## Conventions

- **A baseline lists findings, not a count.** A count accepts any finding once
  the number is high enough, so retiring one accepted case silently makes room
  for a new defect. A stale entry fails for the same reason: left in place it
  pre-accepts whatever next takes that name.
- **Every exception carries its reason, and the condition that would end it.**
  A rule is only as good as its reason, and reasons expire — this repository has
  already had an exclusion whose stated cause became false while the rule kept
  working, hiding 21 undocumented declarations.
- **Do not raise a threshold to make the suite green.** Where a maximum is
  currently exceeded, the file says so and says why the number is real debt.
