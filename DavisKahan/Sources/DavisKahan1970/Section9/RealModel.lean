/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/

import DavisKahan.SpectralTheory.FormMethod.BeamSection9Real

/-!
# Davis--Kahan 1970, Section 9: real free-beam source model

This module is the paper-facing surface for the analytic model used in the numerical example.
It exposes the real `L²(0,1)` free-beam realization, its identification as the self-adjoint
closure of the classical fourth derivative with the four printed free-end boundary conditions,
the increasing positive spectral sequence above `500`, and the exact finite Rayleigh--Ritz data.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970
namespace Section9

noncomputable section

/-- The real Hilbert space used by the Section 9 numerical example. -/
abbrev RealBeamL2 : Type :=
  DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.BeamL2

/-- The self-adjoint real free-beam operator used by the Section 9 numerical example. -/
abbrev realBeamOperator :
    DavisKahanExt.ClosedOperator (𝕜 := ℝ) (E := RealBeamL2) :=
  DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.beamOperator

/-- The classical free-end fourth-derivative graph whose closure is `realBeamOperator`. -/
abbrev realClassicalFreeBeamGraph : Set (RealBeamL2 × RealBeamL2) :=
  DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.classicalFreeBeamGraph

/-- **Paper-faithful operator model for Section 9.**

The real free-beam realization is self-adjoint and is exactly the graph closure of the
classical fourth derivative on functions satisfying
`u''(0)=u'''(0)=u''(1)=u'''(1)=0`. -/
theorem real_freeBeam_operator_source :
    realBeamOperator.IsSelfAdjoint ∧
      closure realClassicalFreeBeamGraph =
        (realBeamOperator.toLinearPMap.graph : Set (RealBeamL2 × RealBeamL2)) :=
  DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.beamOperator_is_closure_of_classical_freeBeam_fourthDerivative

/-- **Paper-faithful spectral model for Section 9.**

Besides the two-dimensional zero eigenspace, the real spectrum is an increasing sequence of
positive eigenvalues, every one of which is larger than `500`. -/
theorem real_freeBeam_spectrum_source :
    realBeamOperator.realSpectrum =
        insert 0 DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.beamEigenvalues ∧
      (∃ f : ℕ → ℝ, StrictMono f ∧
        Set.range f =
          DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.beamEigenvalues ∧
        ∀ n, 500 < f n ∧ f n ∈ realBeamOperator.realSpectrum) := by
  exact ⟨
    DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.realSpectrum_beamOperator_eq_insert_zero,
    DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.exists_strictMono_range_eq_beamEigenvalues⟩

/-- The paper's positive free-beam spectral values are exactly the fourth powers of the
positive roots of `cos beta * cosh beta = 1`. -/
theorem real_freeBeam_positive_spectrum_source :
    DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.beamEigenvalues =
      {lam : ℝ | ∃ beta : ℝ, 0 < beta ∧
        DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.characteristic beta = 0 ∧
        lam = beta ^ 4} :=
  DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.beamRealPositiveSpectrum_sourceFacts

/-- The paper's affine zero-mode plane is contained in the real beam-operator domain. -/
theorem real_freeBeam_trial_le_domain {x : RealBeamL2}
    (hx : x ∈ DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.beamTrial) :
    x ∈ realBeamOperator.domain :=
  DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.beamTrial_le_domain hx

/-- The real free-beam operator annihilates every vector in the paper's affine trial plane. -/
theorem real_freeBeam_operator_apply_trial {x : RealBeamL2}
    (hx : x ∈ DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.beamTrial)
    (hdom : x ∈ realBeamOperator.domain) :
    realBeamOperator.toLinearMap ⟨x, hdom⟩ = 0 :=
  DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.beamOperator_apply_trial hx hdom

/-- The zero eigenspace is exactly the paper's two-dimensional affine trial plane. -/
theorem real_freeBeam_zero_mode_source :
    Module.finrank ℝ
        DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.beamTrial = 2 ∧
      ∀ (x : RealBeamL2) (h : x ∈ realBeamOperator.domain),
        realBeamOperator.toLinearMap ⟨x, h⟩ = 0 ↔
          x ∈ DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.beamTrial :=
  DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.beamRealZeroMode_sourceFacts

/-- The exact finite-data certificate for the paper's real Section 9 model. -/
def real_freeBeam_finiteData_source (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    FreeBeamFiniteDataCertificate ε :=
  DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.beamFiniteDataCertificate ε hε hε100

/-- The real multiplication perturbation and orthonormal affine trial plane satisfy the
source hypotheses used by the finite Section 9 calculation. -/
theorem real_freeBeam_trial_and_perturbation_source (ε : ℝ) (hε : 0 < ε) :
    DavisKahan.IsSelfAdjointOperator
        (DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.beamPerturbation ε) ∧
      ‖DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.beamPerturbation ε‖ ≤ ε ∧
      (‖DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.centeredAffineLp trialOne‖ ^ 2 = 1 ∧
        ‖DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.centeredAffineLp trialTwo‖ ^ 2 = 1 ∧
        ⟪DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.centeredAffineLp trialOne,
          DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.centeredAffineLp trialTwo⟫_ℝ = 0) :=
  DavisKahan.Experimental.MathAhead.HiddenFoundations.FreeBeam.Model.Real.beamRealFiniteData_sourceFacts ε hε

end

end Section9
end DavisKahan1970
end TauCeti
