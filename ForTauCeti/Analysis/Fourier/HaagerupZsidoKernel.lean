/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import ForTauCeti.Analysis.Fourier.ExponentialAbs
public import ForTauCeti.Analysis.Fourier.Poisson.CauchyLattice
public import ForTauCeti.Analysis.SpecialFunctions.Integral.RationalQuadratic
public import ForTauCeti.Analysis.SpecialFunctions.Integral.SineLaplace
public import ForTauCeti.Analysis.Fourier.HaagerupZsido.Defs
public import ForTauCeti.Analysis.Fourier.HaagerupZsido.Integrability
public import ForTauCeti.Analysis.Fourier.HaagerupZsido.Fourier

/-!
# The Haagerup--Zsidó reciprocal Fourier kernel (aggregate)

This module is a transitional re-export aggregate.  The former single-file
development of the scalar Haagerup--Zsidó reciprocal Fourier kernel was split
into seven topic modules; this file re-exports all of them so that existing
consumers importing `ForTauCeti.Analysis.Fourier.HaagerupZsidoKernel` continue
to see the entire `TauCeti.HaagerupZsido` API unchanged.

The split modules are:

* `ForTauCeti.Analysis.Fourier.ExponentialAbs` — exponential Fourier transform;
* `ForTauCeti.Analysis.Fourier.Poisson.CauchyLattice` — lattice sums / Poisson;
* `ForTauCeti.Analysis.SpecialFunctions.Integral.RationalQuadratic` —
  rational quadratic integrals;
* `ForTauCeti.Analysis.SpecialFunctions.Integral.SineLaplace` — sine--Laplace
  integrals;
* `ForTauCeti.Analysis.Fourier.HaagerupZsido.Defs` — kernel definitions and
  elementary API;
* `ForTauCeti.Analysis.Fourier.HaagerupZsido.Integrability` — kernel
  integrability and exact `L¹` mass;
* `ForTauCeti.Analysis.Fourier.HaagerupZsido.Fourier` — the exterior Fourier
  identity.
-/
