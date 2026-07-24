# dev/alternates — non-building historical proof records

Lean files preserved verbatim for proof-strategy comparison that are **known
not to elaborate** on the pinned toolchain and are therefore kept outside all
Lean build roots (the alternate-preservation rule requires `Alternates/`
entries to compile; these do not qualify).

- `RectangularSingularValuesDkVariant.lean` — the `dk-work`-branch variant of
  the rectangular adjoint-spectrum layer (GPT-5.6 High).  Its own header
  documents the `whnf` heartbeat blow-up that the preferred
  `ForTauCeti/Analysis/InnerProductSpace/RectangularSingularValues.lean`
  rewrote around.  It was previously hidden in `ForMathlib/` (built via
  aggregate, never imported); the Wave-1 migration moved it here because
  `ForTauCeti` builds by glob.
