/-
Entry point for the Acharyya et al. 2025 DKPS concentration scaffold.

This library is intentionally separate from `Acharyya2024`: the 2024 paper is
asymptotic consistency of DKPS/raw-stress MDS, while the 2025 paper is finite-
sample concentration. This file depends on `Acharyya2024.Common` for shared finite
matrix/configuration definitions only.
-/

module

public import Acharyya2025.Deterministic
public import Acharyya2025.MathlibBridge
public import Acharyya2025.Bridge
public import Acharyya2025.SpectralPipeline
public import Acharyya2025.GramRealization
public import Acharyya2025.GramRigidity
public import Acharyya2025.Weyl
public import Acharyya2025.OperatorBridge
public import Acharyya2025.DavisKahan
public import Acharyya2025.RankGap
public import Acharyya2025.Overlap
public import Acharyya2025.PolarFactor
public import Acharyya2025.ConfigPerturbation
public import Acharyya2025.MatrixPerturbation
public import Acharyya2025.AlignedPipeline
public import Acharyya2025.SpectralMeasurability
public import Acharyya2025.RateChain
public import Acharyya2025.GrowingPipeline
