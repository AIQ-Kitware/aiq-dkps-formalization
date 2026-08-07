/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
import DavisKahan.InfiniteDimensional.TanTwoTheta.QuarterAcuteFormGap

/-!
# Dimension-free quarter-angle branch (promoted; this module is now a shim)

The mathematics that used to live here is proved in the production tree at
`DavisKahan.InfiniteDimensional.TanTwoTheta.QuarterAcuteFormGap`, where the
default build covers it.  Nothing was restated: the file moved and its
namespace changed from `TauCeti.DavisKahan.FinishTanTwoTheta` to
`TauCeti.DavisKahan`.

This module keeps the lane's historical names available so the lane aggregate
and its audits continue to mean what they meant.
-/

namespace TauCeti
namespace DavisKahan
namespace FinishTanTwoTheta

/-- Promoted to `TauCeti.DavisKahan.reflected_centered_form_lower`. -/
alias reflected_centered_form_lower := TauCeti.DavisKahan.reflected_centered_form_lower

/-- Promoted to
`TauCeti.DavisKahan.reflection_anticommutes_of_maps_orthogonal`. -/
alias reflection_anticommutes_of_maps_orthogonal :=
  TauCeti.DavisKahan.reflection_anticommutes_of_maps_orthogonal

/-- Promoted to `TauCeti.DavisKahan.spectrum_re_lower_of_coercive`. -/
alias spectrum_re_lower_of_coercive := TauCeti.DavisKahan.spectrum_re_lower_of_coercive

/-- Promoted to
`TauCeti.DavisKahan.isQuarterAcute_of_paper_form_gap_infinite`. -/
alias isQuarterAcute_of_paper_form_gap_infinite :=
  TauCeti.DavisKahan.isQuarterAcute_of_paper_form_gap_infinite

end FinishTanTwoTheta
end DavisKahan
end TauCeti
