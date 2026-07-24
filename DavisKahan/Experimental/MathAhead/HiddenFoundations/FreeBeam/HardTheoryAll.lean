/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Abstract.PositiveSurjectiveCriterion
import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Abstract.BoundedInverseRealization
import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Abstract.CompactGraphEmbedding
import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Abstract.TraceKernelModel
import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Abstract.GraphClosedness
import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Abstract.MaximalDomainTransport
import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Abstract.CoerciveFormResolvent
import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Abstract.FormCompactness
import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Abstract.BoundedGraphCompactness
import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Classical.CharacteristicConverse
import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Classical.ModeData
import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Classical.AffineModes
import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Classical.RootLocalizationReduction
import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Analytic.ShiftedBeamRealization
import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Analytic.EigenmodeReduction
import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Analytic.FoundationAssembler

/-!
# Aggregate import for the hard free-beam campaign

Promoted out of the scratch staging area into the `MathAhead` tree.  Every
module below elaborates and is free of proof-escape terms.  The campaign is
reduction machinery: it derives symmetry, self-adjointness, compact resolvent,
and the `> 500` spectral bound from a concrete interval Sobolev space, coercive
form, and numerical root-localization datum, which remain the open concrete
inputs packaged as structure fields.
-/
