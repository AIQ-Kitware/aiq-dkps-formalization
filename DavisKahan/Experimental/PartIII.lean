/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.FullPartIII
import DavisKahan.Experimental.FiniteDimensional.All
import DavisKahan.Experimental.InfiniteDimensional.All
import DavisKahan.Experimental.InfiniteDimensional.SpectraBridge.All

/-!
# Part III manuscript components not yet on the production surface

The production manuscript surface is `FullPartIII`, every alias of which is
proved and reachable from production modules alone.  The aliases here are the
remainder, and they are of two kinds:

* components whose declarations still depend on an open obligation, as
  reported by the dependency probe over the manuscript surface; and
* components that are already proved but whose proofs still live inside a
  module that carries unrelated open obligations, so extracting them is a
  matter of splitting a file rather than of mathematics.

The second kind is the work queue: each one becomes a production alias as soon
as its declaration is separated from the obligations it shares a file with.  Do
not read membership here as a claim that a component is unproved.
-/

namespace ForMathlib
namespace DavisKahan1970

/-! ## Bounded spectral calculus and operator angles -/
alias bounded_spectralProjection := DavisKahanExt.spectralProjection
alias bounded_spectralSubspace := DavisKahanExt.spectralSubspace
alias bounded_borelFunctionalCalculus :=
  DavisKahanExt.boundedBorelFunctionalCalculus
alias bounded_spectralProjection_comp :=
  DavisKahanExt.spectralProjection_comp
alias bounded_spectralProjection_compl :=
  DavisKahanExt.spectralProjection_compl
alias bounded_spectralProjection_countableAdditivity :=
  DavisKahanExt.spectralProjection_stronglyCountablyAdditive
alias bounded_operatorAngle := DavisKahanExt.angleOperator
alias bounded_sinAngleOperator := DavisKahanExt.sinAngleOperator
alias bounded_cosAngleOperator := DavisKahanExt.cosAngleOperator
alias bounded_tanAngleOperator := DavisKahanExt.tanAngleOperator
alias bounded_sinTwoAngleOperator := DavisKahanExt.sinTwoAngleOperator
alias bounded_tanTwoAngleOperator := DavisKahanExt.tanTwoAngleOperator
alias bounded_sinAngle_norm := DavisKahanExt.norm_sinAngleOperator
alias bounded_acute_graph_representation :=
  DavisKahanExt.acute_iff_exists_bounded_angularOperator

/-! ## Sylvester engine -/
alias bounded_sylvester_ordered :=
  DavisKahanExt.norm_sylvester_le_of_orderedSeparation
alias bounded_sylvester_general :=
  DavisKahanExt.norm_sylvester_le_of_generalSeparation
alias bounded_sylvester_solution := DavisKahanExt.sylvester_solve
alias bounded_sylvester_uniqueness := DavisKahanExt.sylvester_unique
alias bounded_sylvester_resolvent_solution :=
  DavisKahanExt.rieszProjection_eq_spectralProjection
alias unbounded_sylvester_ordered :=
  DavisKahan.Experimental.ExactSinTheta.unbounded_sylvester_mem_and_gauge_le_viaKyFan
alias unbounded_sylvester_general :=
  DavisKahan.Experimental.ExactSinTheta.unbounded_sylvester_mem_and_gauge_le_of_gap

/-! ## Single-angle theorems -/
alias bounded_generalizedSinTheta := DavisKahan.Experimental.ExactSinTheta.generalizedSinTheta_bounded
alias bounded_sinTheta := DavisKahan.Experimental.ExactSinTheta.sinTheta_bounded
alias bounded_generalizedSinTheta_exact :=
  DavisKahan.Experimental.ExactSinTheta.generalizedSinTheta_bounded_exact
alias bounded_sinTheta_exact := DavisKahan.Experimental.ExactSinTheta.sinTheta_bounded_exact
alias bounded_sinTheta_residual := DavisKahanExt.sinTheta_residual
alias bounded_sinTheta_perturbation := DavisKahanExt.sinTheta_perturbation
alias bounded_sinTheta_symmetric := DavisKahanExt.sinTheta_symmetric
alias bounded_sinTheta_generalSeparation :=
  DavisKahanExt.sinTheta_generalSeparation
alias bounded_spectralProjection_sinTheta :=
  DavisKahanExt.spectralProjection_sinTheta
alias bounded_ideal_sinTheta := DavisKahanExt.ideal_sinTheta

/-! ## Direct rotation -/
alias bounded_directRotation := DavisKahanExt.directRotation
alias bounded_directRotation_unitary := DavisKahanExt.directRotation_unitary
alias bounded_directRotation_maps_subspace :=
  DavisKahanExt.directRotation_maps_subspace
alias bounded_directRotation_intertwines :=
  DavisKahanExt.directRotation_intertwines
alias bounded_directRotation_sq := DavisKahanExt.directRotation_sq
alias bounded_directRotation_minimal := DavisKahanExt.directRotation_minimal

/-! ## Double-angle and off-diagonal theorems -/
alias bounded_sinTwoTheta_reflectionDefect :=
  DavisKahanExt.sinTwoTheta_reflectionDefect
alias bounded_sinTwoTheta_residual := DavisKahanExt.sinTwoTheta_residual
alias bounded_sinTwoTheta_perturbation :=
  DavisKahanExt.sinTwoTheta_perturbation
alias bounded_sinTwoTheta_generalSeparation :=
  DavisKahanExt.sinTwoTheta_generalSeparation
alias bounded_ideal_sinTwoTheta := DavisKahanExt.ideal_sinTwoTheta
alias bounded_offDiagonal_gap_preservation :=
  DavisKahanExt.gap_preserved_of_offDiagonal
alias bounded_tanTwoTheta_offDiagonal :=
  DavisKahanExt.tanTwoTheta_offDiagonal
alias bounded_aPrioriTanTheta := DavisKahanExt.aPrioriTanTheta
alias bounded_spectral_repulsion :=
  DavisKahanExt.spectral_repulsion_offDiagonal

/-! ## Graph and Riccati theory -/
alias graph_unique_angularOperator := DavisKahanExt.existsUnique_angularOperator
alias bounded_riccati_blockDiagonalization :=
  DavisKahanExt.blockDiagonalization_of_riccati
alias unbounded_riccati_blockDiagonalization :=
  DavisKahanExt.unbounded_blockDiagonalization

/-! ## Unbounded and form theorems -/
alias unbounded_selfAdjoint_spectralProjection :=
  DavisKahanExt.ClosedOperator.spectralProjection
alias unbounded_boundedPerturbation_selfAdjoint :=
  DavisKahanExt.ClosedOperator.isSelfAdjoint_addBounded
alias unbounded_relativePerturbation_selfAdjoint :=
  DavisKahanExt.ClosedOperator.isSelfAdjoint_of_relativelyBounded
alias unbounded_sinTheta_boundedPerturbation :=
  DavisKahanExt.ClosedOperator.sinTheta_unbounded_boundedPerturbation
alias unbounded_generalizedSinTheta :=
  DavisKahan.Experimental.ExactSinTheta.generalizedSinTheta_unbounded
alias unbounded_sinTheta := DavisKahan.Experimental.ExactSinTheta.sinTheta_unbounded
alias unbounded_generalizedSinTheta_exact :=
  DavisKahan.Experimental.ExactSinTheta.generalizedSinTheta_unbounded_exact
alias unbounded_sinTheta_exact := DavisKahan.Experimental.ExactSinTheta.sinTheta_unbounded_exact
alias form_sum_selfAdjoint := DavisKahanExt.klmn
alias form_sinTheta := DavisKahanExt.sinTheta_formPerturbation

/-! ## Continuation, ideal, and sharpness package -/
alias continuedProjection_continuous :=
  DavisKahanExt.continuous_continuedProjection
alias continuedProjection_eq_spectralProjection :=
  DavisKahanExt.continuedProjection_eq_spectralProjection
alias compact_projection_difference :=
  DavisKahanExt.compact_projection_difference
alias schatten_sinTheta := DavisKahanExt.schatten_sinTheta
alias covariance_subspace_sinTheta :=
  DavisKahanExt.covariance_subspace_sinTheta
alias planar_sinTheta_equality := DavisKahanExt.sinTheta_planar_equality
alias planar_sinTwoTheta_asymptoticSharpness :=
  DavisKahanExt.sinTwoTheta_planar_asymptotically_sharp
alias squareRootTwo_threshold_sharp := DavisKahanExt.sqrtTwo_threshold_sharp
alias ideal_planar_extremizer := DavisKahanExt.ideal_planar_extremizer

/-! ## Finite Section 4 and sharpness statements -/
alias finite_directRotation_reversal := DavisKahanTheory.directRotation_symm
alias finite_directRotation_sq := DavisKahanTheory.directRotation_sq
alias finite_directRotation_unique := DavisKahanTheory.directRotation_unique
alias finite_directRotation_displacementSquare_minimal :=
  DavisKahanTheory.directRotation_minimizes_displacementSquare_uiNorm
alias finite_directRotation_uiNorm_minimal :=
  DavisKahanTheory.directRotation_minimizes_uiNorm_of_largestAngle_le_pi_div_three
alias finite_directRotation_opNorm_minimal :=
  DavisKahanTheory.directRotation_minimizes_max_displacement
alias finite_directRotation_basisDisplacement_minimal :=
  DavisKahanTheory.directRotation_minimizes_sum_sq_basis_angles
alias finite_sinTheta_constant_optimal :=
  DavisKahanTheory.sinTheta_constant_optimal
alias finite_sinTwoTheta_constant_optimal :=
  DavisKahanTheory.sinTwoTheta_constant_optimal

alias bounded_sylvester_intervalExterior_genuineSpectrum :=
  DavisKahanExt.norm_sylvester_le_of_spectrum_intervalExterior
alias bounded_sinTheta_genuineSpectrum :=
  DavisKahanExt.sinTheta_genuineSpectrum
alias bounded_sinTheta_genuineSpectrum_symmetric :=
  DavisKahanExt.sinTheta_genuineSpectrum_symmetric
alias bounded_sylvester_intervalExterior_uiNorm_genuineSpectrum :=
  DavisKahanExt.mem_and_gauge_sylvester_le_of_spectrum_intervalExterior
alias bounded_sinTheta_uiNorm_genuineSpectrum :=
  DavisKahanExt.sinTheta_genuineSpectrum_gauge
alias bounded_sinTheta_uiNorm_genuineSpectrum_symmetric :=
  DavisKahanExt.sinTheta_genuineSpectrum_gauge_symmetric
alias bounded_sinTwoTheta_genuineSpectrum :=
  DavisKahanExt.sinTwoTheta_genuineSpectrum
alias bounded_sinTwoTheta_genuineSpectrum_sinAngle :=
  DavisKahanExt.sinTwoTheta_genuineSpectrum_sinAngle
alias bounded_sinTwoTheta_uiNorm_genuineSpectrum :=
  DavisKahanExt.sinTwoTheta_genuineSpectrum_gauge
alias bounded_tanTheta_genuineSpectrum :=
  DavisKahanExt.tanTheta_genuineSpectrum
alias bounded_formBounds_of_spectrum_Icc :=
  DavisKahanExt.formBounds_of_compress_spectrum_subset_Icc
alias bounded_coercive_of_spectrum_exterior :=
  DavisKahanExt.coercive_of_compress_spectrum_exterior
alias bounded_reflectionDefect_offdiag :=
  DavisKahanExt.reflectionDefect_eq_neg_two_smul_offdiag
alias bounded_reflectionDefect_le_cross :=
  DavisKahanExt.norm_reflectionDefect_le_two_mul_norm_cross
alias bounded_sinTwoTheta_genuineSpectrum_defect :=
  DavisKahanExt.sinTwoTheta_genuineSpectrum_defect
alias bounded_cross_le_residual :=
  DavisKahanExt.norm_cross_le_norm_residual
alias bounded_sinTwoTheta_genuineSpectrum_residual :=
  DavisKahanExt.sinTwoTheta_genuineSpectrum_residual
alias bounded_sinTwoAngle_gap_identification :=
  DavisKahanExt.subspaceGap_map_reflection_eq_norm_sinTwoAngle
alias bounded_sinTwoTheta_genuineSpectrum_operator :=
  DavisKahanExt.sinTwoTheta_genuineSpectrum_operator
alias bounded_sinTwoTheta_genuineSpectrum_residual_operator :=
  DavisKahanExt.sinTwoTheta_genuineSpectrum_residual_operator
alias graph_subspace := DavisKahanExt.graphSubspace
alias graph_projection_operator := DavisKahanExt.graphProjectionFormula
alias graph_projection_formula := DavisKahanExt.projection_graphSubspace_formula
alias graph_gap_value :=
  DavisKahanExt.norm_projection_sub_projection_graphSubspace
alias graph_subspaceGap := DavisKahanExt.subspaceGap_graphSubspace
alias graph_tan_maximalAngle :=
  DavisKahanExt.tan_maximalAngle_eq_norm_angularOperator
alias graph_contractive_iff_quarterAcute :=
  DavisKahanExt.norm_angularOperator_lt_one_iff
alias bounded_riccati_graph_equivalence :=
  DavisKahanExt.graph_reduces_iff_solvesRiccati
alias bounded_riccati_existence :=
  DavisKahanExt.exists_riccati_solution_of_gap
alias bounded_riccati_bound := DavisKahanExt.norm_riccati_solution_le
alias bounded_riccati_uniqueness :=
  DavisKahanExt.unique_contractive_riccati_solution
alias unbounded_riccati_existence := DavisKahanExt.exists_strongRiccati_solution
alias close_projections_unitarily_equivalent :=
  DavisKahanExt.range_equiv_of_projection_norm_lt_one

end DavisKahan1970
end ForMathlib
