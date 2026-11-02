/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Core

/-!
# The paper library's spelling of the approximation-number foundation

**Every declaration here is a forwarding name.**  The mathematics lives in
`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/Core.lean` under the generic
namespace `TauCeti.ApproximationNumber`; this module re-exports it under
`TauCeti.DavisKahan.ExactSinTheta`, which is the name 339 references in this
library already use.

## Why the split

The module was lifted into `ForTauCeti` because its imports are `ForTauCeti` leaves and
Mathlib — it is generic approximation-number theory.  But it carried the enclosing
namespace `TauCeti.DavisKahan.ExactSinTheta` with it: **a paper's name and a
staging word, inside the library staged for Tau Ceti.**  A submission reviewer reads
`Experimental` as a warning.

Renaming the namespace outright is not available: it is *shared*, not owned — 283 of its
references across `DavisKahan` are `namespace`/`open`/`end` lines belonging to other
modules.  So the generic library gets the generic name and the paper library keeps its
spelling, which is the same division of labour as
`DavisKahan/BoundedOperator/Compat.lean`.

**Do not add mathematics to this file.**  A new approximation-number result belongs in
`ForTauCeti` under `TauCeti.ApproximationNumber`; if this library wants the shorter name,
add it to the `export` list below.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: this path held the mathematics itself until it moved to `ForTauCeti`.
* Extraction class: **not for extraction** — this is paper-library vocabulary.
-/

public section

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

export TauCeti.ApproximationNumber (
  StronglyTendsto IsOrthogonalProjectionMap
  IsOrthogonalProjectionMap.norm_apply_le IsOrthogonalProjectionMap.norm_le_one tendsto_opNorm_zero_of_finiteDimensional
  approximationSingularValue_comp_le_of_isOrthogonalProjection approximationSingularValue_comp_strongProjection_tendsto_of_minMax approximationSingularValue_comp_strongProjection_tendsto_complex
  kyFanApproximationGauge_comp_strongProjection_tendsto_of_minMax
    kyFanApproximationGauge_comp_strongProjection_tendsto_complex
)

end ExactSinTheta
end DavisKahan
end TauCeti
