/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.Scratch.FreeBeam.Abstract.PositiveSurjectiveCriterion
import DavisKahan.Experimental.Scratch.FreeBeam.Abstract.BoundedInverseRealization
import DavisKahan.Experimental.Scratch.FreeBeam.Abstract.CompactGraphEmbedding
import DavisKahan.Experimental.Scratch.FreeBeam.Abstract.TraceKernelModel
import DavisKahan.Experimental.Scratch.FreeBeam.Abstract.GraphClosedness
import DavisKahan.Experimental.Scratch.FreeBeam.Abstract.MaximalDomainTransport
import DavisKahan.Experimental.Scratch.FreeBeam.Abstract.CoerciveFormResolvent
import DavisKahan.Experimental.Scratch.FreeBeam.Abstract.FormCompactness
import DavisKahan.Experimental.Scratch.FreeBeam.Abstract.BoundedGraphCompactness
import DavisKahan.Experimental.Scratch.FreeBeam.Classical.CharacteristicConverse
import DavisKahan.Experimental.Scratch.FreeBeam.Classical.ModeData
import DavisKahan.Experimental.Scratch.FreeBeam.Classical.AffineModes
import DavisKahan.Experimental.Scratch.FreeBeam.Classical.RootLocalizationReduction
import DavisKahan.Experimental.Scratch.FreeBeam.Analytic.ShiftedBeamRealization
import DavisKahan.Experimental.Scratch.FreeBeam.Analytic.EigenmodeReduction
import DavisKahan.Experimental.Scratch.FreeBeam.Analytic.FoundationAssembler

/-!
# Aggregate import for the hard free-beam scratch campaign

This file intentionally remains separate from the existing compiled
`Scratch.FreeBeam.All` aggregate until a Lean-enabled agent has repaired and
certified every new module.
-/
