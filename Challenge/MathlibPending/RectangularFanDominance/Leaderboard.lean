/-
# Rectangular Fan dominance and two-sided orbit majorization
  -- dependency audit only

These are flagship reusable matrix-analysis results developed for the sharp
Davis--Kahan proof. They currently receive a leaderboard-only dependency audit
because their public vocabulary and implementations still cohabit
`RectangularUINorm.lean`; splitting a clean Mathlib-only conformance surface is
future PR-shaping work.
-/

import ForTauCeti.Analysis.InnerProductSpace.RectangularUnitarilyInvariantNorm

#print axioms TauCeti.DavisKahanTheory.RectangularUnitarilyInvariantNorm.mem_convexHull_twoSidedUnitaryOrbit_of_kyFanSum_le
#print axioms TauCeti.DavisKahanTheory.RectangularUnitarilyInvariantNorm.apply_le_of_kyFanSum_le
