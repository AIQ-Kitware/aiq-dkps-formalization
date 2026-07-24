/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.Sources.DavisKahan1970.Section8.CompressionRepulsion
import DavisKahan.Experimental.Sources.DavisKahan1970.Section8.SelectedBranch
import DavisKahan.Experimental.Sources.DavisKahan1970.Section8.Smallness
import DavisKahan.Experimental.Sources.DavisKahan1970.Section8.SourceSurface

/-! # `DavisKahan/Experimental/Sources/DavisKahan1970/Section8`

Davis--Kahan 1970 Section 8 continuation and branch-selection surface.

This package lives under `Experimental` rather than alongside `Section9` in
`DavisKahan/Sources` because `SelectedBranch` and `SourceSurface` import
`DavisKahan.Experimental.InfiniteDimensional`.  Four modules on that import
path have never compiled, so this aggregate does not build; the Lean
namespaces are still `TauCeti.DavisKahan1970.Section8`, unchanged by the
move.  Promote the package back into `DavisKahan/Sources/DavisKahan1970`
once its dependencies compile. -/
