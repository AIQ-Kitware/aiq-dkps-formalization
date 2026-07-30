/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.All
import DavisKahan.Experimental.Sources.All

/-! # Experimental Davis--Kahan theory

**The canonical infinite-dimensional route is the production tree, not this one.**
`Experimental/InfiniteDimensional/` still holds the older ambient facades, kept for
historical reference; they are deliberately not aggregated here, and the live
development is `DavisKahan.All` together with `Geometry.Angle.*`, `TanTwoTheta.All`
and `DoubleAngle.{Unbounded,UnboundedIdeal}`, all of which `DavisKahan.All` reaches.

That statement used to live in `Experimental/InfiniteDimensional/All.lean`, an
aggregate whose every import was already reachable from the `DavisKahan.All` it
opened with — so it contributed nothing but the note, while its own 94-module
directory went unaggregated and it stood as a permanent rule-3 violation.  The note
is the part worth keeping; the sub-aggregates (`InfiniteDimensional/Core/All.lean`
and its siblings) cover the subtree.
-/
