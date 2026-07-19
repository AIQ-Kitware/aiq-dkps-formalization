/-
Copyright (c) 2026 Spectra Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import Spectra.QuantumMechanics.BornRule.Joint.Forward
import Spectra.ProjValMeasure.GeneralMap

/-!
# The joint projective measure as a genuine PVM

The joint-measure construction is packaged in `Joint.Forward` as a POVM plus
an independently proved projectivity law.  This file combines those two pieces
into `ProjValMeasure'`, then pushes it forward along real-valued joint symbols.
The difference symbol is the spectral carrier needed by the Hilbert--Schmidt
Sylvester multiplier.
-/

open MeasureTheory Complex
open scoped InnerProductSpace

namespace Spectra

noncomputable section

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [MeasurableSpace ι]

namespace POVM

/-- A projective POVM, bundled as a general projection-valued measure. -/
noncomputable def toProjValMeasure' (M : POVM H ι)
    (hM : M.IsProjective) : ProjValMeasure' H ι where
  proj := M.effect
  diag := M.diag
  diag_finite := M.diag_finite
  inner_proj := M.inner_effect
  proj_univ := M.effect_univ
  proj_inter := hM

@[simp]
theorem toProjValMeasure'_proj (M : POVM H ι)
    (hM : M.IsProjective) (B : Set ι) (hB : MeasurableSet B) :
    (M.toProjValMeasure' hM).proj B hB = M.effect B hB :=
  rfl

@[simp]
theorem toProjValMeasure'_diag (M : POVM H ι)
    (hM : M.IsProjective) (ξ : H) :
    (M.toProjValMeasure' hM).diag ξ = M.diag ξ :=
  rfl

end POVM

namespace QuantumMechanics.BornRule

open Operator

/-- The canonical joint PVM of two strongly commuting observables. -/
noncomputable def jointPVM
    (A B : SelfAdjointOperator H) (hSC : StronglyCommute A B) :
    ProjValMeasure' H (ℝ × ℝ) :=
  (jointPOVM A B hSC).toProjValMeasure'
    (jointPOVM_isProjective A B hSC)

@[simp]
theorem jointPVM_diag
    (A B : SelfAdjointOperator H) (hSC : StronglyCommute A B)
    (ξ : H) :
    (jointPVM A B hSC).diag ξ = jointScalarMeasure A B hSC ξ :=
  rfl

/-- The one-dimensional PVM obtained from the joint PVM by the difference
symbol `(lambda, alpha) |-> lambda - alpha`. -/
noncomputable def jointDifferencePVM
    (A B : SelfAdjointOperator H) (hSC : StronglyCommute A B) :
    ProjValMeasure H :=
  (jointPVM A B hSC).mapToReal
    (fun p : ℝ × ℝ => p.1 - p.2)
    (measurable_fst.sub measurable_snd)

@[simp]
theorem jointDifferencePVM_diag
    (A B : SelfAdjointOperator H) (hSC : StronglyCommute A B)
    (ξ : H) :
    (jointDifferencePVM A B hSC).diag ξ =
      (jointScalarMeasure A B hSC ξ).map
        (fun p : ℝ × ℝ => p.1 - p.2) :=
  rfl


/-- The characteristic function of the pushed-forward difference measure is
implemented by the product of the two commuting unitary groups. -/
theorem integral_exp_difference_jointScalarMeasure
    (A B : SelfAdjointOperator H) (hSC : StronglyCommute A B)
    (ξ : H) (t : ℝ) :
    ∫ p : ℝ × ℝ, Complex.exp (Complex.I * ((p.1 - p.2 : ℝ) : ℂ) * (t : ℂ))
        ∂(jointScalarMeasure A B hSC ξ) =
      ⟪ξ,
        (YosidaHille.genToGroup A.selfAdjoint).U t
          ((YosidaHille.genToGroup B.selfAdjoint).U (-t) ξ)⟫_ℂ := by
  have hprod := joint_product_form A B hSC
    (SpectralTheory.char_measurable t) (SpectralTheory.char_bdd t)
    (SpectralTheory.char_measurable (-t)) (SpectralTheory.char_bdd (-t)) ξ
  rw [SpectralTheory.spectralCalculus_char,
    SpectralTheory.spectralCalculus_char] at hprod
  rw [← hprod]
  apply integral_congr_ae
  filter_upwards [] with p
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

end QuantumMechanics.BornRule
end
end Spectra
