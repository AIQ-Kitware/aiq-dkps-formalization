# Historical record: Section 3 spectral multiplicity campaign

**Status: completed.**  This file used to be the execution plan for closing the
spectral-multiplicity phrasing of Davis--Kahan Section 3.  It is retained because
the source census cites its construction record, not because it owns current
work.

Current status belongs to:

- `dev/davis-kahan-1970-full-source-census.json` and its generated Markdown;
- `dev/davis-kahan-1970-frontier.json` and its generated status view;
- the production modules under `DavisKahan/Geometry/Halmos/` and
  `ForTauCeti/Analysis/InnerProductSpace/LinearPMap/BorelCalculus/`.

Do not use the former TODO ordering or agent assignments from Git history as a
work queue.

## What landed

The campaign closed the gap between the operator-invariant classification of an
ordered pair of subspaces and the paper's spectral-multiplicity phrasing.  The
reusable layer includes the measure-class relation, relabelling and restriction
unitaries for `L²`, countable slice assembly, multiplicity level sets and normal
forms, operator unitary equivalence, Hilbert-sum intertwining, separable cyclic
spectral models, and multiplicity-model existence/uniqueness infrastructure.

The paper-facing Section 3 statements are now represented in the maintained
Davis--Kahan source census and frontier rather than in this plan.

## Section 7 — construction record cited by the census

The implementation assembled the following admission-free reusable pieces in
`ForTauCeti` (names may move while preserving their public declarations):

- `MeasureClass.lean` — measure-class equivalence;
- `LpComp.lean` — relabelling unitaries and intertwining;
- `LpRestrict.lean` — extension by zero and measurable-partition decomposition;
- `LpSliceSum.lean` — assembly of countably many multiplication models;
- `MultiplicityLevels.lean` — dominating measure, rank, level sets, normal form;
- `OperatorUnitaryEquiv.lean` and `HilbertSumIntertwine.lean`;
- `BorelCalculus/SeparableCyclic.lean`;
- `BorelCalculus/MultiplicityModel.lean`.

The invariant is encoded by a finite measure together with an antitone sequence
of measurable multiplicity level sets, modulo measure-class and almost-everywhere
agreement.  This is the durable mathematical design result that the old plan was
needed to discover.

## Validation

```bash
python3 scripts/check_davis_kahan_1970_source_census.py
python3 scripts/check_davis_kahan_frontier.py
```

When Lean is available, use the census probe/build rather than this historical
record to decide whether declarations still resolve.
