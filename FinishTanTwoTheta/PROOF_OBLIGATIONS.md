# Proof obligations

## Bounded target - discharged

The bounded completion target
`TauCeti.DavisKahan.paperFaithful_tanTwoTheta_uiNorm` is compiled and promoted into
`DavisKahan/InfiniteDimensional/TanTwoTheta/PaperFaithfulUINorm.lean`, which is
reachable from the production Davis--Kahan aggregate.

The theorem has:

- no `FiniteDimensional` or finite-carrier hypothesis;
- a derived strict quarter-angle branch;
- the canonical ambient `tanTwoAngleOperatorC` conclusion;
- source-ideal membership and the sharp factor-two estimate against the full
  perturbation.

The former finishing module is retained only as a compatibility alias/regression
surface.

## Remaining separate research target

`FinishTanTwoTheta/FinishTanTwoTheta/DavisKahan/Unbounded.lean` studies an
unrestricted unbounded analogue. It is intentionally not imported by the bounded
aggregate and is not part of the discharged bounded obligation.

## Validation

For changes to the compatibility package, run:

```bash
lake build FinishTanTwoTheta
```

For the production theorem, validate through the normal Davis--Kahan build/gates.
The legacy `verify_grounding.py` scans the intentionally separate unbounded research
file as well, so its exit status is not a bounded-target completion signal.
