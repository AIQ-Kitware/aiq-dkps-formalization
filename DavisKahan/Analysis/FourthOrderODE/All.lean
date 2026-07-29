/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Analysis.FourthOrderODE.SmoothGreenIdentity
import DavisKahan.Analysis.FourthOrderODE.ComplexGreenIdentity
import DavisKahan.Analysis.FourthOrderODE.SmoothKernel
import DavisKahan.Analysis.FourthOrderODE.AffineModes

/-! # `DavisKahan/Analysis/FourthOrderODE`

Fourth-order Lagrange/Green identities on `[0,1]` and the free-end kernel
characterisation `u'''' = 0`.  Mathlib-only dependencies. -/
