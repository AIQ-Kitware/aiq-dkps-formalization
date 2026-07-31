/-
# Approximation numbers and finite Ky Fan gauges -- dependency audit

This directory carries a `Leaderboard.lean` and **no `Conformance.lean` and no
`comparator/*.json`, deliberately**: it is a leaderboard-only dependency audit,
not a posed challenge.

**Two of the five have since been promoted and are named accordingly.**  The
complex strong-cutoff and complex Ky Fan triangle theorems now live in
`ForTauCeti` under `TauCeti.ApproximationNumber`, inside `defaultTargets`; the
three `ApproximationNumbersReal` statements are still in the paper library's
`DavisKahan.Experimental.ExactSinTheta` namespace, outside `defaultTargets`, so
there is still no stable public statement to pose a conformance against for
those.  Pose the challenge for a theorem after it is promoted, not before.

**The names below are the canonical ones, not the re-exported spellings.**  The
paper library keeps its own names for the promoted pair through an `export`, and
that alias resolves in Lean — but `scripts/check_declaration_name_drift.py`
indexes declarations rather than following `export`, so an audit written against
the alias passes the compiler and fails the drift check.  Naming the declaration
where it is defined is both what the checker wants and what a reader wants.

Note that this audits a tree the default build does not compile.  The names are
checked by `scripts/check_declaration_name_drift.py`, which is what keeps this
file from silently pointing at nothing.
-/
import DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

#print axioms TauCeti.ApproximationNumber.approximationSingularValue_comp_strongProjection_tendsto_complex
#print axioms TauCeti.DavisKahan.Experimental.ExactSinTheta.ApproximationNumbersReal.approximationNumber_isLUB_finiteRestrictions_real
#print axioms TauCeti.DavisKahan.Experimental.ExactSinTheta.ApproximationNumbersReal.approximationSingularValue_comp_strongProjection_tendsto_real
#print axioms TauCeti.ApproximationNumber.kyFanApproximationGauge_add_le_complex
#print axioms TauCeti.DavisKahan.Experimental.ExactSinTheta.ApproximationNumbersReal.kyFanApproximationGauge_add_le_real
