/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 Thinking
-/
import DavisKahan.Riccati.BoundedSharpEstimates

/-!
# The near-singular-pair estimate for bounded tangent-two-theta (promoted)

**Promoted 2026-07-30 under lane `EXP-PROMOTE-T2T` slice 1.**
`riccati_near_singular_pair_bound` now lives in its source-facing home,
`DavisKahan/Riccati/BoundedSharpEstimates.lean`, alongside the other sharp
bounded Riccati estimates, and is compiled by `defaultTargets` — which this
module never was.

Nothing is restated here.  The theorem keeps its name and namespace
(`TauCeti.DavisKahanExt`), so importing this module still supplies it and the
sibling `BoundedRiccatiNorm.lean` needs no edit.  This file remains only as that
re-export and should be deleted once the rest of the
`Experimental/InfiniteDimensional/TanTwoTheta` group is promoted.

The mathematics, unchanged: a near norm-attaining right/left singular pair for a
contractive Riccati solution yields the factor `1 - s * t`, with the error term
measuring exactly the defect in the adjoint singular relation `X⋆ y = t x`.
-/
