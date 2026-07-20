/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperAll
import DavisKahan.Sources.DavisKahan1970.GeneralSinTheta

/-!
# Literal Davis--Kahan 1970 sine-theta surface

This source facade names every sine-theta declaration needed for a line-by-line
comparison with Sections 1 and 6 and the unbounded appendix of the paper.  The
previous `GeneralSinTheta` facade remains the accepted central theorem.  This
module adds the exact source norm, source angle, symmetric theorem, second
generalized theorem, common-domain forms, and optimality statements.
-/

namespace ForMathlib
namespace DavisKahan1970

namespace Exact := DavisKahan.Experimental.ExactSinTheta

/-! ## Source norm class -/

alias UnitaryInvariantNorm := Exact.PaperUnitaryInvariantNorm
alias SymmetricNormingFunction := Exact.PaperSymmetricNormingFunction
alias unitaryInvariantNorm_equiv_symmetricNormingFunction :=
  Exact.PaperSymmetricNormingFunction.paperNormEquiv
alias unitaryInvariantNorm_operator_laws :=
  Exact.PaperUnitaryInvariantNorm.gauge_comp_le
alias unitaryInvariantNorm_definite :=
  Exact.PaperUnitaryInvariantNorm.gauge_eq_zero_iff
alias nuclearNorm := Exact.paperNuclearNorm
alias unitaryInvariantNorm_nonempty := Exact.paperUnitaryInvariantNorm_nonempty

/-! ## Literal angle objects -/

alias directedCosineBlock := Exact.paperCosineBlockC
alias directedSineBlock := Exact.paperSineBlockC
alias directedCosineOperator := Exact.paperCosineModulusC
alias directedAngle := Exact.paperSourceDirectedAngleC
alias directedSinAngle := Exact.paperSourceDirectedSinC
alias directedCosAngle := Exact.paperSourceDirectedCosC
alias directedCosAngle_eq_modulus := Exact.paperSourceDirectedCosC_eq
alias directedSinAngle_eq_modulus :=
  Exact.paperSourceDirectedSinC_eq_paperSineModulusC
alias directedSinAngle_singularValues :=
  Exact.paperSourceDirectedSin_same_paperSineBlock
alias directedAngle_eq_arcsin_sineModulus :=
  Exact.paperSourceDirectedAngleC_eq_arcsin_sineModulus
alias directedAngle_real_eq_arcsin_sineModulus :=
  Exact.paperSourceDirectedAngleR_eq_arcsin_sineModulus
alias directedAngle_real := Exact.paperSourceDirectedAngleR
alias directedSinAngle_real := Exact.paperSourceDirectedSinR
alias directedCosAngle_real := Exact.paperSourceDirectedCosR
alias fullAngleCoordinates := Exact.paperSourceFullAngleC
alias fullSinAngleCoordinates := Exact.paperSourceFullSinC
alias fullSinAngle_singularValues_projectionDifference :=
  Exact.paperSourceFullSin_same_projectionDifference
alias fullSinAngle_norm_projectionDifference :=
  Exact.paperSourceFullSin_mem_iff_and_gauge_eq
alias ambientEquivalentAngle := DavisKahanExt.paperAngleOperatorC
alias ambientEquivalentSinAngle := DavisKahanExt.paperSinAngleOperatorC
alias ambientEquivalentSinAngle_eq_projectionDifferenceSine :=
  DavisKahanExt.paperSinAngleOperatorC_eq
alias fullAngleCoordinates_real := Exact.paperSourceFullAngleR
alias fullSinAngleCoordinates_real := Exact.paperSourceFullSinR

/-! ## Lemmas 6.1 and 6.2 -/

alias lemma6_1_kyFan := Exact.paperLemma61_all_kyFan
alias lemma6_1 := Exact.paperLemma61_every_unitarilyInvariantNorm
alias lemma6_1_converse := Exact.paperLemma61_converse
alias lemma6_2 := Exact.PaperUnitaryInvariantNorm.paperDiagonalPair_paperGauge_le
alias lemma6_2_kyFan := Exact.paperDiagonalPair_all_kyFan_le

/-! ## Original and generalized sine theorems -/

alias GeneralSinThetaIdealFamilyProblem := Exact.PaperGeneralSinThetaProblem
alias IsometricSinThetaIdealFamilyProblem := Exact.PaperIsometricSinThetaProblem
alias RealGeneralSinThetaIdealFamilyProblem := Exact.PaperRealGeneralSinThetaProblem
alias RealIsometricSinThetaIdealFamilyProblem := Exact.PaperRealIsometricSinThetaProblem
alias generalizedSinTheta_idealFamily := Exact.PaperGeneralSinThetaProblem.result
alias sinTheta_idealFamily := Exact.PaperIsometricSinThetaProblem.result
alias generalizedSinTheta_real_idealFamily :=
  Exact.PaperRealGeneralSinThetaProblem.result
alias sinTheta_real_idealFamily := Exact.PaperRealIsometricSinThetaProblem.result

alias IsometricSinThetaPaperData := Exact.PaperIsometricTheoremData
alias sinTheta_exactPaper :=
  Exact.PaperIsometricTheoremData.result_every_unitarilyInvariantNorm_across
alias RealIsometricSinThetaPaperData := Exact.PaperRealIsometricTheoremData
alias sinTheta_real_exactPaper :=
  Exact.PaperRealIsometricTheoremData.result_every_unitarilyInvariantNorm_across

alias Theorem6_1Data := Exact.PaperTheorem61Data
alias Theorem6_1 :=
  Exact.PaperTheorem61Data.result_every_unitarilyInvariantNorm_across
alias Theorem6_1RealData := Exact.PaperRealTheorem61Data
alias Theorem6_1_real :=
  Exact.PaperRealTheorem61Data.result_every_unitarilyInvariantNorm_across
alias generalizedSinTheta_exactPaper :=
  Exact.PaperTheorem61Data.result_every_unitarilyInvariantNorm_across
alias generalizedSinTheta_real_exactPaper :=
  Exact.PaperRealTheorem61Data.result_every_unitarilyInvariantNorm_across

/-! ## Proposition 6.1 -/

alias SymmetricSinThetaProblem := Exact.PaperSymmetricSinThetaProblem
alias Proposition6_1 :=
  Exact.PaperSymmetricSinThetaProblem.result_every_unitarilyInvariantNorm

/-! ## Theorem 6.2 and its printed finite-rank consequence -/

alias PairwiseSpectrumGap := Exact.GenuinePairwiseSpectrumGap
alias Theorem6_2Data := Exact.PaperTheorem62Data
alias Theorem6_2 := Exact.PaperTheorem62Data.result_across
alias Theorem6_2_boundNorm_of_finiteRank :=
  Exact.PaperTheorem62Data.operatorNorm_result_across_of_rank_le
alias Theorem6_2RealData := Exact.PaperRealTheorem62Data
alias Theorem6_2_real := Exact.PaperRealTheorem62Data.result_across
alias Theorem6_2_real_boundNorm_of_finiteRank :=
  Exact.PaperRealTheorem62Data.operatorNorm_result_across_of_rank_le

/-! ## Exact unbounded appendix forms -/

alias HasCommonDomain := Exact.HasPaperCommonDomain
alias CommonDomainSinThetaData := Exact.PaperCommonDomainSinThetaData
alias CommonDomainTheorem6_1Data := Exact.PaperCommonDomainTheorem61Data
alias Theorem6_1_commonDomain :=
  Exact.PaperCommonDomainTheorem61Data.result_every_unitarilyInvariantNorm_across
alias CommonDomainTheorem6_2Data := Exact.PaperCommonDomainTheorem62Data
alias Theorem6_2_commonDomain := Exact.PaperCommonDomainTheorem62Data.result_across
alias Theorem6_2_commonDomain_boundNorm_of_finiteRank :=
  Exact.PaperCommonDomainTheorem62Data.operatorNorm_result_of_rank_le
alias RealCommonDomainTheorem6_1Data :=
  Exact.PaperRealCommonDomainTheorem61Data
alias Theorem6_1_real_commonDomain :=
  Exact.PaperRealCommonDomainTheorem61Data.result_every_unitarilyInvariantNorm_across
alias RealCommonDomainTheorem6_2Data :=
  Exact.PaperRealCommonDomainTheorem62Data
alias Theorem6_2_real_commonDomain :=
  Exact.PaperRealCommonDomainTheorem62Data.result_across
alias Theorem6_2_real_commonDomain_boundNorm_of_finiteRank :=
  Exact.PaperRealCommonDomainTheorem62Data.operatorNorm_result_of_rank_le

/-! ## Graph-core appendix forms -/

alias IsGraphCore := Exact.ClosedOperator.IsGraphCore
alias CommonCoreResidualData := Exact.PaperCommonCoreResidualData
alias commonCoreResidual_extends_to_domain :=
  Exact.PaperCommonCoreResidualData.extends_to_domain
alias CommonCoreTheorem6_1Data := Exact.PaperCommonCoreTheorem61Data
alias Theorem6_1_commonCore :=
  Exact.PaperCommonCoreTheorem61Data.result_every_unitarilyInvariantNorm_across
alias CommonCoreTheorem6_2Data := Exact.PaperCommonCoreTheorem62Data
alias Theorem6_2_commonCore := Exact.PaperCommonCoreTheorem62Data.result_across
alias RealCommonCoreTheorem6_1Data := Exact.PaperRealCommonCoreTheorem61Data
alias Theorem6_1_real_commonCore :=
  Exact.PaperRealCommonCoreTheorem61Data.result_every_unitarilyInvariantNorm_across
alias RealCommonCoreTheorem6_2Data := Exact.PaperRealCommonCoreTheorem62Data
alias Theorem6_2_real_commonCore :=
  Exact.PaperRealCommonCoreTheorem62Data.result_across

/-! ## Sharpness and necessity -/

alias Theorem6_1_equality_every_norm :=
  Exact.paperTheorem61_planar_equality_every_norm
alias sineTheta_constant_one_optimal := Exact.paperSinTheta_constant_one_optimal
alias oneGap_counterexample_sine_squareNorm :=
  Exact.paperCounterexample_sine_square_norm
alias oneGap_counterexample_perturbation_squareNorm :=
  Exact.paperCounterexample_perturbation_square_norm
alias oneGap_does_not_imply_Proposition6_1 :=
  Exact.paperOneGap_does_not_imply_symmetric_square_estimate

end DavisKahan1970
end ForMathlib
