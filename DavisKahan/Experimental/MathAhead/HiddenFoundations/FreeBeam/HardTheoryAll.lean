/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.SpectralTheory.FormMethod.PositiveSurjectiveCriterion
import DavisKahan.SpectralTheory.FormMethod.BoundedInverseRealization
import DavisKahan.SpectralTheory.FormMethod.CompactGraphEmbedding
import DavisKahan.SpectralTheory.FormMethod.TraceKernelModel
import DavisKahan.SpectralTheory.FormMethod.GraphClosedness
import DavisKahan.SpectralTheory.FormMethod.MaximalDomainTransport
import DavisKahan.SpectralTheory.FormMethod.CoerciveFormResolvent
import DavisKahan.SpectralTheory.FormMethod.FormCompactness
import DavisKahan.SpectralTheory.FormMethod.BoundedGraphCompactness
import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Classical.CharacteristicConverse
import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Classical.ModeData
import DavisKahan.Analysis.FourthOrderODE.AffineModes
import DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Classical.RootLocalizationReduction
import DavisKahan.SpectralTheory.FormMethod.ShiftedBeamRealization
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
