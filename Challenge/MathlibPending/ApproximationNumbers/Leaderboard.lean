/-
# Approximation numbers and finite Ky Fan gauges -- dependency audit

This directory carries a `Leaderboard.lean` and **no `Conformance.lean` and no
`comparator/*.json`, deliberately**: it is a leaderboard-only dependency audit,
not a posed challenge.  The five theorems below live in the
`DavisKahan.Experimental.ExactSinTheta` namespace, which sits outside
`defaultTargets`, so there is no stable public statement to pose a conformance
against until that material is promoted.  Promotion is tracked by the
`EXP-PROMOTE-*` lanes in `dev/LANES.md`; pose the challenge after it lands, not
before.

Note that this audits a tree the default build does not compile.  The names are
checked by `scripts/check_declaration_name_drift.py`, which is what keeps this
file from silently pointing at nothing.
-/
import DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

#print axioms TauCeti.DavisKahan.Experimental.ExactSinTheta.approximationSingularValue_comp_strongProjection_tendsto_complex
#print axioms TauCeti.DavisKahan.Experimental.ExactSinTheta.ApproximationNumbersReal.approximationNumber_isLUB_finiteRestrictions_real
#print axioms TauCeti.DavisKahan.Experimental.ExactSinTheta.ApproximationNumbersReal.approximationSingularValue_comp_strongProjection_tendsto_real
#print axioms TauCeti.DavisKahan.Experimental.ExactSinTheta.kyFanApproximationGauge_add_le_complex
#print axioms TauCeti.DavisKahan.Experimental.ExactSinTheta.ApproximationNumbersReal.kyFanApproximationGauge_add_le_real
