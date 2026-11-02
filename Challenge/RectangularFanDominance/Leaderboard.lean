/-
# Rectangular Fan dominance and two-sided orbit majorization
  -- dependency audit only

These results use the canonical rectangular seminorm and two-sided orbit API.
This leaderboard audits their proof dependencies; it does not compare their
signatures against an independent conformance module.
-/

module

public import TauCeti.Analysis.InnerProductSpace.FanDominance

public section

#print axioms LinearMap.mem_twoSidedUnitaryOrbitHull_iff_kyFanSum_le
#print axioms TauCeti.UnitarilyInvariantSeminorm.map_le_of_kyFanSum_le
