/-
Entry point for the Acharyya et al. 2024 DKPS consistency scaffold.

This library is intentionally separate from `Acharyya2025`: the 2024 paper is
asymptotic consistency of DKPS/raw-stress MDS, while the 2025 paper is finite-
sample concentration. Keeping them separate makes dependency direction and audit
status clearer.
-/

module

public import Acharyya2024.WellKnown
public import Acharyya2024.Common
public import Acharyya2024.GrowingModels
public import Acharyya2024.ProfileNonuniqueness
public import Acharyya2024.ContinuousMDS
public import Acharyya2024.Consistency

public import Acharyya2024.Probability
public import Acharyya2024.SecondMoment
public import Acharyya2024.RawStress
