/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.PartIII
import DavisKahan.Sources.DavisKahan1970.GeneralSinTheta
import DavisKahan.Alternative.All
import DavisKahan.DoubleAngle.All
import DavisKahan.FiniteDimensional.All
import DavisKahan.Geometry.All
import DavisKahan.Interop.All
import DavisKahan.OperatorIdeal.All
import DavisKahan.Riccati.All
import DavisKahan.SinTheta.All
import DavisKahan.Specialized.All
import DavisKahan.SpectralTheory.All
import DavisKahan.Sylvester.All
import DavisKahan.TanTheta.All
import DavisKahan.TanTwoTheta.All

/-!
# Full Davis--Kahan 1970 Part III proof-manuscript surface

This source module names the theorem package targeted by the one-shot proof
manuscript.  The stable finite results remain available through `PartIII`.

Every alias below is proved: each resolves to a declaration whose axiom
dependencies are exactly `propext`, `Classical.choice` and `Quot.sound`.  The
manuscript components that are still open are named separately, in
`DavisKahan.Experimental.PartIII`, so that importing this file cannot pull an
unproved result into a production build.

The mathematical dependency order and per-declaration repair ledger are in
`dev/davis-kahan-1970-one-shot-proof-manuscript.md`.
-/

namespace ForMathlib
namespace DavisKahan1970

/-! ## Canonical single-angle target

The unqualified source role belongs to the generalized unbounded theorem.
The bounded aliases below are specializations and implementation seams. -/
alias canonical_generalizedSinTheta := generalizedSinTheta
alias canonical_sinTheta := sinTheta
alias canonical_generalizedSinTheta_complementaryBlock :=
  generalizedSinTheta_complementaryBlock

/-! ## Sylvester engine -/
alias bounded_sylvester_neumann_solution :=
  DavisKahan.Experimental.ExactSinTheta.sylvesterNeumannSolution_eq

/-! ## Single-angle theorems -/
alias unbounded_sinTheta_opNorm :=
  DavisKahan.Experimental.ExactSinTheta.sinTheta_unbounded_opNorm
alias unbounded_sylvester_intervalExterior_opNorm :=
  DavisKahan.Experimental.ExactSinTheta.norm_closedSylvester_le_of_intervalExterior
alias unbounded_sylvester_exteriorInterval_opNorm :=
  DavisKahan.Experimental.ExactSinTheta.norm_closedSylvester_le_of_exteriorInterval
alias unbounded_sinTheta_uiNorm :=
  DavisKahan.Experimental.ExactSinTheta.sinTheta_unbounded_gauge
alias unbounded_sinTheta_opNorm_genuineSpectrum :=
  DavisKahan.Experimental.SpectraBridge.sinTheta_unbounded_opNorm_of_spectrum_gap
alias unbounded_boundedPerturbation_sinTheta_spectralSubspaces :=
  DavisKahan.Experimental.SpectraBridge.sinTheta_addBounded_spectralSubspaces_opNorm_of_intervalExterior
alias unbounded_boundedPerturbation_sinTheta_directedGap :=
  DavisKahan.Experimental.SpectraBridge.sinTheta_addBounded_directedGap_of_intervalExterior
alias unbounded_boundedPerturbation_sinTheta_spectralProjections :=
  DavisKahan.Experimental.SpectraBridge.sinTheta_addBounded_spectralProjection_sub_opNorm_of_spectrum_gap
alias unbounded_spectralRestriction_formBounds :=
  DavisKahan.Experimental.SpectraBridge.selfAdjointSpectralRestriction_semibounded_of_subset_Icc
alias unbounded_spectralRestriction_spectrum_exterior :=
  DavisKahan.Experimental.SpectraBridge.selfAdjointSpectralRestriction_spectrum_avoids_open_of_inter_eq_empty
alias unbounded_sinTheta_uiNorm_genuineSpectrum :=
  DavisKahan.Experimental.SpectraBridge.sinTheta_unbounded_gauge_of_spectrum_gap
alias unbounded_sylvester_exteriorInterval_uiNorm :=
  DavisKahan.Experimental.ExactSinTheta.mem_and_gauge_le_of_exteriorLeft_intervalRight
alias unbounded_sylvester_intervalExterior_uiNorm :=
  DavisKahan.Experimental.ExactSinTheta.mem_and_gauge_le_of_boundedLeft_exteriorRight
alias unbounded_boundedRealization_of_spectrum_Icc :=
  DavisKahan.Experimental.ExactSinTheta.exists_boundedRealization_of_spectrum_subset_Icc
alias unbounded_semibounded_of_spectrum_Icc :=
  DavisKahan.Experimental.SpectraBridge.semibounded_of_spectrum_subset_Icc
alias unbounded_sylvester_exteriorInterval_uiNorm_genuineSpectrum :=
  DavisKahan.Experimental.SpectraBridge.unbounded_sylvester_mem_and_gauge_le_of_spectra_exteriorLeft_intervalRight
alias unbounded_sylvester_intervalExterior_uiNorm_genuineSpectrum :=
  DavisKahan.Experimental.SpectraBridge.unbounded_sylvester_mem_and_gauge_le_of_spectra_intervalLeft_exteriorRight
alias real_sinTheta_symmetric_genuineSpectrum :=
  DavisKahan.Experimental.Foundation.RealSpectralBridge.opNorm_starProjection_sub_le_of_restriction_spectra
alias real_upperFormBound_of_spectrum :=
  DavisKahan.Experimental.Foundation.RealSpectralBridge.upperFormBoundOn_top_of_spectrum_subset_Iic
alias bounded_sinAngleOperatorC_norm := DavisKahanExt.norm_sinAngleOperatorC
alias bounded_sinAngleOperatorDirectedC_norm :=
  DavisKahanExt.norm_sinAngleOperatorDirectedC
alias bounded_angle_pythagoras :=
  DavisKahanExt.sinAngleOperatorDirectedC_sq_add_cosAngleOperatorC_sq
alias bounded_angle_commute :=
  DavisKahanExt.commute_sinAngleOperatorDirectedC_cosAngleOperatorC
alias bounded_sinTwoAngleOperatorC := DavisKahanExt.sinTwoAngleOperatorC
alias bounded_sinTwoAngleOperatorC_norm_le :=
  DavisKahanExt.norm_sinTwoAngleOperatorC_le
alias bounded_cosAngle_coercive :=
  DavisKahanExt.norm_cosAngleOperatorC_apply_ge
alias bounded_cosAngle_injective_of_acute :=
  DavisKahanExt.cosAngleOperatorC_eq_zero_imp_of_acute
alias bounded_cosAngleExtended_invertible :=
  DavisKahanExt.cosAngleExtendedC_ker_bot_range_top
alias bounded_tanAngleOperatorC := DavisKahanExt.tanAngleOperatorC
alias bounded_tanAngle_defining_identity :=
  DavisKahanExt.tanAngleOperatorC_comp_cosAngleExtendedC
alias bounded_cosTwoAngleOperatorC := DavisKahanExt.cosTwoAngleOperatorC
alias bounded_cosTwoAngle_coercive :=
  DavisKahanExt.norm_cosTwoAngleOperatorC_apply_ge
alias bounded_cosTwoAngleExtended_invertible :=
  DavisKahanExt.cosTwoAngleExtendedC_ker_bot_range_top
alias bounded_tanTwoAngleOperatorC := DavisKahanExt.tanTwoAngleOperatorC
alias bounded_tanTwoAngle_defining_identity :=
  DavisKahanExt.tanTwoAngleOperatorC_comp_cosTwoAngleExtendedC
alias bounded_tanAngle_norm_le := DavisKahanExt.norm_tanAngleOperatorC_le
alias bounded_tanTheta_perVector := DavisKahanExt.tan_theta_le'
alias bounded_sinTwoAngle_norm_eq :=
  DavisKahanExt.norm_sinTwoAngleOperatorC

/-! ## Direct rotation -/
alias complex_directRotation :=
  DavisKahan.Experimental.SpectraBridge.spectraDirectRotation
alias complex_directRotation_sq :=
  DavisKahan.Experimental.SpectraBridge.spectraDirectRotation_sq
alias complex_directRotation_reversal :=
  DavisKahan.Experimental.SpectraBridge.spectraDirectRotation_reversal
alias complex_directRotation_unique :=
  DavisKahan.Experimental.SpectraBridge.spectraDirectRotation_unique
alias complex_directRotation_minimal :=
  DavisKahan.Experimental.SpectraBridge.spectraDirectRotation_minimal

/-! ## Graph and Riccati theory -/
alias bounded_coercive_isUnit :=
  ForMathlib.ContinuousLinearMap.isUnit_of_coercive
alias bounded_one_add_star_mul_self_isUnit :=
  ForMathlib.ContinuousLinearMap.isUnit_one_add_star_mul_self
alias bounded_positive_cauchy_schwarz :=
  ForMathlib.ContinuousLinearMap.norm_apply_sq_le_of_positive
alias bounded_inverse_defect_norm :=
  ForMathlib.ContinuousLinearMap.norm_one_sub_inverse_one_add

/-! ## Unbounded and form theorems -/
alias unbounded_boundedPerturbation_selfAdjoint_spectra :=
  DavisKahan.Experimental.SpectraBridge.addBounded_isSelfAdjoint
alias unbounded_spectralRestriction :=
  DavisKahan.Experimental.SpectraBridge.selfAdjointSpectralRestriction
alias unbounded_spectralRestriction_selfAdjoint :=
  DavisKahan.Experimental.SpectraBridge.selfAdjointSpectralRestriction_isSelfAdjoint
alias unbounded_sinTheta_boundedPerturbation_blockEmbeddings :=
  DavisKahan.Experimental.SpectraBridge.sinTheta_addBounded_opNorm_of_spectrum_gap_isometric
alias unbounded_sinTheta_boundedPerturbation_spectralSubspaces :=
  DavisKahan.Experimental.SpectraBridge.sinTheta_addBounded_spectralSubspaces_opNorm_of_spectrum_gap

/-! ## Continuation, ideal, and sharpness package -/

end DavisKahan1970
end ForMathlib
