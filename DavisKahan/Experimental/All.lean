/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.All
import DavisKahan.Experimental.Frontier.All

/-! # Experimental Davis--Kahan theory

## Why there is no `Experimental.Sources.All`

`DavisKahan/Experimental/Sources/**` held the Davis--Kahan 1970 Section 8
package while its import closure still went through modules that did not
compile.  That closure became admission-free and buildable, so the package
moved to `DavisKahan/Sources/DavisKahan1970/Section8/` — exactly the promotion
its own aggregate docstring asked for — and the two `Experimental` aggregates
that existed only to reach it were deleted rather than left as empty shells.
`DavisKahan.All`, imported above, reaches Section 8 now.

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

## Why `Frontier.All` is imported here

`DavisKahan/Experimental/Frontier/**` holds the remaining Davis--Kahan 1970
frontier statements — the Section 3 classification spine, the
infinite-dimensional Section 4 propositions, and the Section 9 analytic model —
together with the `sorry`s that mark what is still open.  Until 2026-08-04
**nothing in the repository imported any of it.**  `lake build` did not reach it,
`lake build DavisKahan.Experimental` did not reach it, and neither did
`Challenge` or `FinishTanTwoTheta`; it compiled only when a module was named
explicitly on the command line, which nothing and nobody did routinely.

That is the same defect the `RoadmapBridge` block in `lakefile.toml` records for
the suggested-signature files: a tree that nothing builds is a tree that rots
silently, and the fix is an import rather than a checker.  It is imported *here*
rather than into a default target because the frontier's whole purpose is to
carry `sorry`s, so it cannot live under `warningAsError`.  `lake build
DavisKahan.Experimental` now covers it.
-/
