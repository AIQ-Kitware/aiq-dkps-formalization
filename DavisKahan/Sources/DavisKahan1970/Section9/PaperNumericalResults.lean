/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/

import DavisKahan.SpectralTheory.FormMethod.BeamWeinberger
import DavisKahan.Sources.DavisKahan1970.Section9.BeamDoubleTangentKyFan

/-!
# Davis--Kahan 1970, Section 9: paper-exact numerical result surface

This module exposes the numerical conclusions of the Section 9 free-beam example
at the paper-facing namespace.  Every premise of these wrappers is discharged by
the genuine beam realization: there are no `TheoremOutputCertificate` fields and
no assumed Weinberger/Lehmann angle estimates.

The historical route to equation (9.8) uses external comparison results.  The
wrapper below instead uses the unconditional beam theorem already proved from the
subsequent, sharper one-vector Davis--Kahan argument, so the printed conclusion is
proved rather than imported as a hypothesis.

The final individual-eigenvector `omega_k` estimates are intentionally not exposed
here yet: their current operator-level theorem has the needed mathematics but still
requires a source-facing eigenvalue-order labeling wrapper.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section9

noncomputable section

open TauCeti.DavisKahan.FreeBeam.Model

/-- **Davis--Kahan 1970, equation (9.1), on the genuine free-beam example.** -/
theorem equation_9_1_source (ε : ℝ) (hε : 0 < ε) (_hε100 : ε < 100) :
    beamSinTheta ε < (811 : ℝ) / 500000 * ε :=
  equation_9_1 ε (beamSinTheta ε) hε (beamSinTheta_le ε)

/-- **Davis--Kahan 1970, equation (9.2), on the genuine free-beam example.** -/
theorem equation_9_2_source (ε : ℝ) (hε : 0 < ε) (_hε100 : ε < 100) :
    beamSinTwoTheta ε < (1 : ℝ) / 250 * ε :=
  equation_9_2 ε (beamSinTwoTheta ε) (beamSinTwoTheta_lt ε hε)

/-- **Davis--Kahan 1970, equation (9.3), on the genuine free-beam example.** -/
theorem equation_9_3_source (ε : ℝ) (hε : 0 < ε) (_hε100 : ε < 100) :
    beamSinThetaSum ε < (109 : ℝ) / 50000 * ε :=
  equation_9_3 ε (beamSinThetaSum ε) hε (beamSinThetaSum_le ε)

/-- **Davis--Kahan 1970, equation (9.4), on the genuine free-beam example.** -/
theorem equation_9_4_source (ε : ℝ) (hε : 0 < ε) (_hε100 : ε < 100) :
    beamSinTwoThetaSum ε < (1 : ℝ) / 125 * ε :=
  equation_9_4 ε (beamSinTwoThetaSum ε) (beamSinTwoThetaSum_lt ε hε)

/-- **Davis--Kahan 1970, equation (9.5).**  Both Rayleigh--Ritz values are exposed
in the same source-facing statement. -/
theorem equation_9_5_source (ε : ℝ) (_hε : 0 < ε) (_hε100 : ε < 100) :
    ritzLow ε = ε / 2 * (1 - (Real.sqrt 3)⁻¹) ∧
      ritzHigh ε = ε / 2 * (1 + (Real.sqrt 3)⁻¹) :=
  ⟨equation_9_5_low ε, equation_9_5_high ε⟩

/-- **Davis--Kahan 1970, equation (9.6), including its two-term Ky Fan sentence.**
Both conclusions are proved for the genuine perturbed beam from `0 < ε < 100`. -/
theorem equation_9_6_source (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanTheta ε
        < ((1291 : ℝ) / 2500000 * ε) /
            (1 - (7887 : ℝ) / 5000000 * ε) ∧
      beamTanThetaSum ε
        < ((1291 : ℝ) / 2500000 * ε) /
            (1 - (7887 : ℝ) / 5000000 * ε) :=
  ⟨beamTanTheta_lt_printed ε hε hε100,
    beamTanThetaSum_lt_printed ε hε hε100⟩

/-- **Davis--Kahan 1970, equation (9.7), including its two-term Ky Fan sentence.**
Both conclusions are proved for the genuine perturbed beam from `0 < ε < 100`. -/
theorem equation_9_7_source (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanTwoTheta ε
        < ((1291 : ℝ) / 1250000 * ε) /
            (1 - (7887 : ℝ) / 5000000 * ε) ∧
      beamTanTwoThetaSum ε
        < ((1291 : ℝ) / 1250000 * ε) /
            (1 - (7887 : ℝ) / 5000000 * ε) :=
  ⟨beamTanTwoTheta_lt_printed ε hε hε100,
    beamTanTwoThetaSum_lt_printed ε hε hε100⟩

/-- **Davis--Kahan 1970, equation (9.8), both displayed individual-vector bounds.**

The paper derives these numbers through Weinberger/Lehmann comparison results.
Here the same printed conclusions are proved unconditionally for the genuine beam
from the later, strictly sharper one-vector Davis--Kahan estimates; no external
comparison theorem is left as a caller-supplied hypothesis. -/
theorem equation_9_8_source (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanPhi ε (centeredAffineLp trialOne)
        < ((1291 : ℝ) / 2500000 * ε) /
            (1 - (4227 : ℝ) / 10000000 * ε) ∧
      beamTanPhi ε (centeredAffineLp trialTwo)
        < ((1291 : ℝ) / 2500000 * ε) /
            (1 - (7887 : ℝ) / 5000000 * ε) :=
  beam_equation_9_8 ε hε hε100

/-- **The sharper one-vector Davis--Kahan bounds immediately following (9.8).**
These are the paper's two displayed `0.0003652` estimates for the specific Ritz
vectors, proved directly for the genuine beam. -/
theorem direct_individual_vector_bounds_source
    (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanPhi ε (centeredAffineLp trialOne)
        < ((913 : ℝ) / 2500000 * ε) /
            (1 - (4227 : ℝ) / 10000000 * ε) ∧
      beamTanPhi ε (centeredAffineLp trialTwo)
        < ((913 : ℝ) / 2500000 * ε) /
            (1 - (7887 : ℝ) / 5000000 * ε) :=
  ⟨beamTanPhi_low_lt_printed ε hε hε100,
    beamTanPhi_high_lt_printed ε hε hε100⟩

end

end Section9
end DavisKahan1970
end TauCeti
