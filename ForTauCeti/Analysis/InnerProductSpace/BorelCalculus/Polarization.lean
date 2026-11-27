/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Basic
public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Polarization

/-!
# Matrix elements of the bounded Borel calculus

The native polarized pairing recovers all matrix elements from diagonal spectral integrals.
-/

public section

open scoped InnerProductSpace

namespace TauCeti.BorelCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The matrix elements of the native calculus are the polarized diagonal integrals. -/
theorem inner_borelCalculus (a : H →L[ℂ] H) [IsStarNormal a]
    (f : BoundedBorelFunction (spectrum ℂ a)) (ψ ξ : H) :
    ⟪ψ, a.borelCalculus f ξ⟫_ℂ = a.pair f ψ ξ := by
  rw [a.pair_def, ← a.inner_borelCalculus_self, ← a.inner_borelCalculus_self,
    ← a.inner_borelCalculus_self, ← a.inner_borelCalculus_self]
  exact (a.borelCalculus f).toLinearMap.inner_polarization ψ ξ |>.symm

end TauCeti.BorelCalculus
