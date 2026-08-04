/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import ForTauCeti.Analysis.InnerProductSpace.YuWangSamworth.Residual
import ForTauCeti.Analysis.InnerProductSpace.YuWangSamworth.Statistics
import ForTauCeti.Analysis.InnerProductSpace.YuWangSamworth.SingularSubspace
import ForTauCeti.Analysis.InnerProductSpace.YuWangSamworth.TopEigenblock
import ForTauCeti.Analysis.InnerProductSpace.AlignedBasis
import ForTauCeti.Analysis.InnerProductSpace.Singular.Subspace
import ForTauCeti.Analysis.InnerProductSpace.TwoDimensionalSingularValues

/-!
# Grounded imports for the Yu--Wang--Samworth completion lane

This module centralizes the existing repository results on which the lane is
allowed to build. New paper-facing proofs should import this module rather than
silently reaching through unrelated experimental trees.
-/
