/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.SpectralTheory.FormMethod.PositiveSurjectiveCriterion
import DavisKahan.SpectralTheory.FormMethod.TraceKernelModel
import DavisKahan.SpectralTheory.FormMethod.BoundedInverseRealization
import DavisKahan.SpectralTheory.FormMethod.GraphClosedness
import DavisKahan.SpectralTheory.FormMethod.MaximalDomainTransport
import DavisKahan.SpectralTheory.FormMethod.CoerciveFormResolvent
import DavisKahan.SpectralTheory.FormMethod.CompactGraphEmbedding
import DavisKahan.SpectralTheory.FormMethod.FormCompactness
import DavisKahan.SpectralTheory.FormMethod.BoundedGraphCompactness
import DavisKahan.SpectralTheory.FormMethod.ShiftedBeamRealization

/-! # `DavisKahan/SpectralTheory/FormMethod`

The form method: a coercive sesquilinear form realises a self-adjoint operator with
compact resolvent.  Promoted out of `Experimental/` on 2026-07-29; production had no
form method, no compactness API and no bounded-to-unbounded inverse construction. -/
