# Agent prompt: compile and complete the full Part III math-ahead batch

Read `dev/full-part-iii-admission-elimination-math-ahead-2026-07-20.md` in full.
The overlay restores 174 exact-signature historical proof bodies and replaces
one unused speculative continuation API with the completed proof-carrying
continuation stack.

Treat the current accepted baseline as immutable:

- the 43-endpoint source Section 6 audit;
- Proposition 6.1 and the Theorem 6.2 chain;
- the independent column-expansion proof;
- the finite-multiplicity equality theorem and injectivity witness;
- the recovered paper Hilbert--Schmidt Sylvester module;
- universe polymorphism and rectangular operator-ideal statements.

Run `python3 scripts/check_full_part_iii_math_ahead.py` after every statement or
proof repair.  It must remain clean.  Do not alter a guarded theorem statement,
add a new hypothesis, collapse a theorem to a bounded or finite specialization,
or reintroduce an unfinished proof term.

Compile the 28 changed Lean modules in the order listed in the handoff.  Use
exit status, not grepped output, as the source of truth.  Do not run concurrent
Lake builds.

The restored bodies come from work-in-progress commit `2244e7c6bd7f`.  They are
not expected to use current APIs perfectly.  When a name is absent:

1. search current production modules and vendored Spectra for the modern
   theorem or construction;
2. rewrite through the canonical current abstraction;
3. add a helper only if it is independently reusable and belongs in the
   canonical module;
4. never create a private parallel spectral calculus, contour representation,
   operator ideal, or closed-operator API merely to make an old body elaborate.

The old `ContinuationRoadmap` declarations are intentionally gone.  Do not
restore them.  The completed replacements are the continuation contour,
transport, spectral-identification, assembly, rotation-chain, selected-branch,
and final theorem modules.

If a guarded statement is false or malformed, stop on that declaration and
provide a concrete mathematical counterexample or a precise type-theoretic
inconsistency.  Do not silently weaken or delete it.  Deletion is allowed only
for an unguarded declaration after proving that it is neither part of the full
Davis--Kahan source correspondence nor independently reusable and that nothing
references it.

After all candidate modules compile, promote every newly complete Experimental
module into a canonical production location.  Repoint imports and source
facades, regenerate aggregates, and do not weaken the structural checker.

Final commands, all sequential:

```bash
python3 scripts/check_full_part_iii_math_ahead.py
python3 scripts/generate_all_aggregates.py --check
lake build
lake build DavisKahan.All
lake build DavisKahan.Experimental
python3 scripts/audit_full_paper_sine_theta.py
python3 scripts/inventory_davis_kahan_debt.py --json
python3 scripts/check_library_structure.py
lake env lean DavisKahan/Alternative/OperatorIdeal/HilbertSchmidt/ColumnExpansion.lean
lake env lean DavisKahan/Sources/DavisKahan1970/SineTheta/FiniteMultiplicity.lean
lake env lean DavisKahan/Sources/DavisKahan1970/Sylvester/PaperHilbertSchmidt.lean
```

Acceptance requires:

- all commands return exit 0;
- the inventory reports only the 18 intentional challenge placeholders;
- the structural checker returns CLEAN, 5/5;
- the paper audit remains CLEAN with exactly 43 targets and the exact permitted
  dependency set;
- all 174 guarded signatures remain unchanged;
- no executable Davis--Kahan source contains an unfinished proof term;
- no canonical alternative proof is replaced by a circular call to the theorem
  it is meant to establish independently.

Report every changed file, each genuine mathematical defect found, which
historical bodies were replaced rather than repaired, all removals and their
justification, command results, and the final commit hash.

## Superseded prompt

Do not execute the all-at-once instructions above.  Use
`dev/full-part-iii-staged-repair-agent-prompt-2026-07-20.md`, which corrects the
false-clean checker and authorizes the minimal general infrastructure actually
missing from the pinned libraries.
