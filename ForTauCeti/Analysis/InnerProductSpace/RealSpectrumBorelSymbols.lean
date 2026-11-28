/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.CStarAlgebra.RealSpectrumFunctionalCalculus
public import TauCeti.MeasureTheory.Function.BoundedBorel.Basic

/-!
# Bounded Borel symbols over the real and complex spectra

The real-spectrum homeomorphism of a self-adjoint operator induces a star algebra equivalence
by precomposition. Both spectra carry their subspace Borel σ-algebras.
-/

public section

namespace TauCeti.BorelCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

/-- The real-spectrum homeomorphism is measurable for the subspace Borel structures. -/
theorem measurable_realSpectrumHomeomorph (ha : IsSelfAdjoint a) :
    Measurable (realSpectrumHomeomorph ha) :=
  (realSpectrumHomeomorph ha).continuous.measurable

/-- The inverse real-spectrum homeomorphism is measurable. -/
theorem measurable_realSpectrumHomeomorph_symm (ha : IsSelfAdjoint a) :
    Measurable (realSpectrumHomeomorph ha).symm :=
  (realSpectrumHomeomorph ha).symm.continuous.measurable

/-- Reindex bounded Borel symbols along the real-spectrum homeomorphism. -/
noncomputable def realSpectrumBorelEquiv (ha : IsSelfAdjoint a) :
    BoundedBorelFunction (spectrum ℝ a) ≃⋆ₐ[ℂ] BoundedBorelFunction (spectrum ℂ a) :=
  StarAlgEquiv.ofStarAlgHom
    (BoundedBorelFunction.compStarAlgHom' (realSpectrumHomeomorph ha)
      (measurable_realSpectrumHomeomorph ha))
    (BoundedBorelFunction.compStarAlgHom' (realSpectrumHomeomorph ha).symm
      (measurable_realSpectrumHomeomorph_symm ha))
    (StarAlgHom.ext fun f => BoundedBorelFunction.ext fun x => by simp)
    (StarAlgHom.ext fun g => BoundedBorelFunction.ext fun z => by simp)

/-- Evaluation of the reindexed symbol at a complex spectral point. -/
@[simp] theorem realSpectrumBorelEquiv_apply (ha : IsSelfAdjoint a)
    (f : BoundedBorelFunction (spectrum ℝ a)) (z : spectrum ℂ a) :
    realSpectrumBorelEquiv ha f z = f (realSpectrumHomeomorph ha z) :=
  BoundedBorelFunction.compStarAlgHom'_apply _ _ f z

/-- Evaluation of the inverse reindexing at a real spectral point. -/
@[simp] theorem realSpectrumBorelEquiv_symm_apply (ha : IsSelfAdjoint a)
    (f : BoundedBorelFunction (spectrum ℂ a)) (x : spectrum ℝ a) :
    (realSpectrumBorelEquiv ha).symm f x = f ((realSpectrumHomeomorph ha).symm x) :=
  BoundedBorelFunction.compStarAlgHom'_apply _ _ f x

end TauCeti.BorelCalculus
