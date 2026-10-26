/-
# Approximation numbers and finite Ky Fan gauges: dependency audit

This directory is a dependency audit, with no separate conformance statement or
comparator configuration. It checks the retained strong-cutoff results, the
finite-restriction LUB consequence over Tau Ceti's native min–max predicate, and
the accepted scalar-generic Ky Fan triangle theorem.
-/
module

public import DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

public section

#print axioms TauCeti.ApproximationNumber.approximationSingularValue_comp_strongProjection_tendsto_complex
#print axioms TauCeti.HasMinMaxLowerBound.approximationNumber_isLUB_finiteRestrictions
#print axioms TauCeti.DavisKahan.ExactSinTheta.ApproximationNumbersReal.approximationSingularValue_comp_strongProjection_tendsto_real
#print axioms ContinuousLinearMap.kyFanGauge_add_le
