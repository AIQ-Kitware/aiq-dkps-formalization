/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Terra
-/
import DavisKahan.SpectralTheory.ClosedOperator.Basic

/-!
# Transitional ClosedOperator boundary

The historical `TauCeti.DavisKahanExt.ClosedOperator` bundle remains available
only while source-facing records and Spectra bridges are converted to raw
`LinearPMap` inputs. Its reusable domain, graph, extension, and Sylvester
mathematics is implemented in the dependency-clean `ForTauCeti` LinearPMap
layer; this module is the downstream import boundary for consumers that still
need the historical bundle.

Do not add new generic theorems to this module. A consumer should import the
canonical `ForTauCeti` API directly whenever its statement can use raw partial
maps. Delete this boundary after the final source/Spectra consumer migrates.
-/
