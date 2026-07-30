/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.General
import DavisKahan.SpectralTheory.BoundedSelfAdjointSpectralProjection

/-!
# The complex instance of the bounded Borel projection hypothesis

`SinTheta/General.lean` carries the bounded Borel functional calculus as a
hypothesis class, `BoundedBorelProjection`, because that calculus is not
available over a general `RCLike` field.  A hypothesis is only worth having if
something satisfies it, so this module discharges it at `𝕜 = ℂ`.

This is the point of stating the leaf as a class rather than as an opaque
`def`: the general `sin Θ` results in `General.lean` now specialise to genuine
theorems about the genuine spectral projections of a bounded self-adjoint
operator on a complex Hilbert space, with no obligation left over.

## Why the instance lives here and not in `General.lean`

`General.lean` is over a general `𝕜`, and `TauCeti.ProjValMeasure` fixes its
scalar field in its own binder (`[InnerProductSpace ℂ H]`).  Declaring the
instance there would drag the whole Borel-calculus import chain into the
generic module for the sake of one specialisation.

It cannot live with the construction either: `BoundedSelfAdjointSpectralProjection.lean`
is production, and production may not import `DavisKahan.Experimental.*`
(dependency-layer rule 4).  A module that mentions both therefore has to sit on
the experimental side of that line, which is where this one is.

## What is actually being checked

Both laws are already theorems on the production side:

* `proj_idem` is the `proj_idem` field of the projection-valued measure;
* `proj_comm` is `TauCeti.BorelCalculus.boundedPVM_proj_comm`, the statement
  that a spectral projection commutes with its own operator.

So the instance is a repackaging, not new mathematics — which is the intended
outcome.  The hypothesis was chosen to demand exactly what a projection-valued
measure already supplies, and no more: it says nothing about countable
additivity or about multiplicativity in `s`, both of which the PVM also has.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Experimental

universe v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **The bounded Borel projection hypothesis holds over `ℂ`**, witnessed by the
genuine spectral measure of the operator.

With this instance in scope, `spectralSubspace`, `spectralProjection`,
`isInvariant_spectralSubspace` and the `sin Θ` estimates built on them are
unconditional statements about complex Hilbert spaces. -/
noncomputable instance boundedBorelProjection_complex :
    BoundedBorelProjection ℂ H where
  proj A hA s hs := boundedSelfAdjointSpectralProjection A hA s hs
  proj_idem A hA s hs := (boundedSelfAdjointSpectralPVM A hA).proj_idem s hs
  proj_comm A hA s hs :=
    TauCeti.BorelCalculus.boundedPVM_proj_comm
      ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mpr hA) s hs

/-- The spectral subspace supplied by the complex instance is the production
one, by definition.  Stated so that results proved in `General.lean` can be
transported onto `boundedSelfAdjointSpectralSubspace` without unfolding. -/
theorem spectralSubspace_eq_boundedSelfAdjointSpectralSubspace
    (A : H →L[ℂ] H) (hA : IsSelfAdjointOperator A)
    (s : Set ℝ) (hs : MeasurableSet s) :
    spectralSubspace A hA s hs = boundedSelfAdjointSpectralSubspace A hA s hs :=
  rfl

end DavisKahanExt
end TauCeti
