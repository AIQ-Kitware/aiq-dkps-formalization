/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.PairShift
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ProjValMeasure.Bounded

public import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley
public import ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.PVM
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Cayley.Basic
public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint

/-!
# Complementary spectral ranges of a self-adjoint partial operator

For the native Cayley spectral measure, the range of the projection on a
complementary Borel set is the orthogonal complement of the original range.

The original DKPS construction followed the Cayley route in Rudin and
Reed–Simon. The contribution census records its relationship to Tau Ceti and
the former Spectra dependency.
-/

public section

open scoped InnerProductSpace
open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The range of the spectral projection on a complement is the orthogonal complement
of the original spectral range. -/
theorem specRange_compl {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ((A.spectralPVM hA).proj Bᶜ hB.compl).range = ((A.spectralPVM hA).proj B hB).rangeᗮ := by
  ext x
  rw [← Submodule.starProjection_eq_self_iff, ← Submodule.starProjection_eq_self_iff,
    ProjValMeasure.starProjection_range_proj, Submodule.starProjection_orthogonal,
    ProjValMeasure.starProjection_range_proj, ProjValMeasure.proj_compl]

end LinearPMap
end TauCeti
