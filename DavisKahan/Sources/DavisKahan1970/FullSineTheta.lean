/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.Ideals.All
import DavisKahan.Sources.DavisKahan1970.SineTheta.All
import DavisKahan.Sources.DavisKahan1970.SineTheta.FiniteMultiplicity
import DavisKahan.Sources.DavisKahan1970.GeneralSinTheta

/-!
# Literal Davis--Kahan 1970 sine-theta surface

This source facade names every sine-theta declaration needed for a line-by-line
comparison with Sections 1 and 6 and the unbounded appendix of the paper.  The
previous `GeneralSinTheta` facade remains the accepted central theorem.  This
module adds the exact source norm, source angle, symmetric theorem, second
generalized theorem, common-domain forms, and optimality statements.
-/

namespace TauCeti
namespace DavisKahan1970

-- Lean has no namespace-alias command, so the paper implementation namespace
-- is opened directly; every unprefixed `Paper...` name below resolves into it.
open DavisKahan.Experimental.ExactSinTheta

/-! ## Source norm class -/

alias UnitaryInvariantNorm := PaperUnitaryInvariantNorm
alias SymmetricNormingFunction := PaperSymmetricNormingFunction
alias unitaryInvariantNorm_equiv_symmetricNormingFunction :=
  PaperSymmetricNormingFunction.paperNormEquiv
alias unitaryInvariantNorm_operator_laws :=
  PaperUnitaryInvariantNorm.gauge_comp_le
alias unitaryInvariantNorm_definite :=
  PaperUnitaryInvariantNorm.gauge_eq_zero_iff
alias nuclearNorm := paperNuclearNorm
alias unitaryInvariantNorm_nonempty := paperUnitaryInvariantNorm_nonempty

/-! ## Literal angle objects -/

alias directedCosineBlock := paperCosineBlockC
alias directedSineBlock := paperSineBlockC
alias directedCosineOperator := paperCosineModulusC
alias directedAngle := paperSourceDirectedAngleC
alias directedSinAngle := paperSourceDirectedSinC
alias directedCosAngle := paperSourceDirectedCosC
alias directedCosAngle_eq_modulus := paperSourceDirectedCosC_eq
alias directedSinAngle_eq_modulus :=
  paperSourceDirectedSinC_eq_paperSineModulusC
alias directedSinAngle_singularValues :=
  paperSourceDirectedSin_same_paperSineBlock
alias directedAngle_eq_arcsin_sineModulus :=
  paperSourceDirectedAngleC_eq_arcsin_sineModulus
alias directedAngle_real_eq_arcsin_sineModulus :=
  paperSourceDirectedAngleR_eq_arcsin_sineModulus
alias directedAngle_real := paperSourceDirectedAngleR
alias directedSinAngle_real := paperSourceDirectedSinR
alias directedCosAngle_real := paperSourceDirectedCosR
alias fullAngleCoordinates := paperSourceFullAngleC
alias fullSinAngleCoordinates := paperSourceFullSinC
alias fullSinAngle_singularValues_projectionDifference :=
  paperSourceFullSin_same_projectionDifference
alias fullSinAngle_norm_projectionDifference :=
  paperSourceFullSin_mem_iff_and_gauge_eq
alias ambientEquivalentAngle := DavisKahanExt.paperAngleOperatorC
alias ambientEquivalentSinAngle := DavisKahanExt.paperSinAngleOperatorC
alias ambientEquivalentSinAngle_eq_projectionDifferenceSine :=
  DavisKahanExt.paperSinAngleOperatorC_eq
alias fullAngleCoordinates_real := paperSourceFullAngleR
alias fullSinAngleCoordinates_real := paperSourceFullSinR

/-! ## Lemmas 6.1 and 6.2 -/

alias lemma6_1_kyFan := paperLemma61_all_kyFan
alias lemma6_1 := paperLemma61_every_unitarilyInvariantNorm
alias lemma6_1_converse := paperLemma61_converse
alias lemma6_2 := paperDiagonalPair_paperGauge_le
alias lemma6_2_kyFan := paperDiagonalPair_all_kyFan_le

/-! ## Original and generalized sine theorems -/

alias GeneralSinThetaIdealFamilyProblem := PaperGeneralSinThetaProblem
alias IsometricSinThetaIdealFamilyProblem := PaperIsometricSinThetaProblem
alias RealGeneralSinThetaIdealFamilyProblem := PaperRealGeneralSinThetaProblem
alias RealIsometricSinThetaIdealFamilyProblem := PaperRealIsometricSinThetaProblem
alias generalizedSinTheta_idealFamily := PaperGeneralSinThetaProblem.result
alias sinTheta_idealFamily := PaperIsometricSinThetaProblem.result
alias generalizedSinTheta_real_idealFamily :=
  PaperRealGeneralSinThetaProblem.result
alias sinTheta_real_idealFamily := PaperRealIsometricSinThetaProblem.result

alias IsometricSinThetaPaperData := PaperIsometricTheoremData
alias sinTheta_exactPaper :=
  PaperIsometricTheoremData.result_every_unitarilyInvariantNorm_across
alias RealIsometricSinThetaPaperData := PaperRealIsometricTheoremData
alias sinTheta_real_exactPaper :=
  PaperRealIsometricTheoremData.result_every_unitarilyInvariantNorm_across

alias Theorem6_1Data := PaperTheorem61Data
alias Theorem6_1 :=
  PaperTheorem61Data.result_every_unitarilyInvariantNorm_across
alias Theorem6_1RealData := PaperRealTheorem61Data
alias Theorem6_1_real :=
  PaperRealTheorem61Data.result_every_unitarilyInvariantNorm_across
alias generalizedSinTheta_exactPaper :=
  PaperTheorem61Data.result_every_unitarilyInvariantNorm_across
alias generalizedSinTheta_real_exactPaper :=
  PaperRealTheorem61Data.result_every_unitarilyInvariantNorm_across

/-! ## Proposition 6.1 -/

alias SymmetricSinThetaProblem := PaperSymmetricSinThetaProblem
alias Proposition6_1 :=
  PaperSymmetricSinThetaProblem.result_every_unitarilyInvariantNorm

-- The real-scalar form.  A unitarily invariant norm sees only the complete
-- singular-value sequence, so the real conclusion is carried by
-- `paperCrossSineSum U V` rather than by a functional-calculus sine: no real
-- continuous functional calculus is needed, and none is assumed.
-- `Proposition6_1_real_sinTheta_singularValues` is the compiled certificate that
-- this operator carries exactly the paper's whole-space `sin Theta` sequence,
-- and `Proposition6_1_real_representative` states the estimate for an arbitrary
-- operator with that sequence.
alias RealSymmetricSinThetaProblem := PaperRealSymmetricSinThetaProblem
alias Proposition6_1_real :=
  PaperRealSymmetricSinThetaProblem.result_every_unitarilyInvariantNorm_real
alias Proposition6_1_real_kyFan :=
  PaperRealSymmetricSinThetaProblem.symmetric_all_kyFan_real
alias Proposition6_1_real_sinTheta_singularValues :=
  PaperRealSymmetricSinThetaProblem.crossSineSum_paperMem_iff_and_gauge_eq
alias Proposition6_1_real_sinTheta_eq_literalFullSinAngle :=
  approximationNumber_paperSourceFullSinR_eq_paperCrossSineSum
alias Proposition6_1_real_representative :=
  PaperRealSymmetricSinThetaProblem.result_every_unitarilyInvariantNorm_representative_real

/-! ## Theorem 6.2 and its printed finite-rank consequence -/

alias PairwiseSpectrumGap := PairwiseSpectrumGap
alias Theorem6_2Data := PaperTheorem62Data
alias Theorem6_2 := PaperTheorem62Data.result_across
alias Theorem6_2_boundNorm_of_finiteRank :=
  PaperTheorem62Data.operatorNorm_result_across_of_rank_le
alias Theorem6_2RealData := PaperRealTheorem62Data
alias Theorem6_2_real := PaperRealTheorem62Data.result_across
alias Theorem6_2_real_boundNorm_of_finiteRank :=
  PaperRealTheorem62Data.operatorNorm_result_across_of_rank_le

/-! ## Exact unbounded appendix forms -/

alias HasCommonDomain := HasPaperCommonDomain
alias CommonDomainSinThetaData := PaperCommonDomainSinThetaData
alias CommonDomainTheorem6_1Data := PaperCommonDomainTheorem61Data
alias Theorem6_1_commonDomain :=
  PaperCommonDomainTheorem61Data.result_every_unitarilyInvariantNorm_across
alias CommonDomainTheorem6_2Data := PaperCommonDomainTheorem62Data
alias Theorem6_2_commonDomain := PaperCommonDomainTheorem62Data.result_across
alias Theorem6_2_commonDomain_boundNorm_of_finiteRank :=
  PaperCommonDomainTheorem62Data.operatorNorm_result_of_rank_le
alias RealCommonDomainTheorem6_1Data :=
  PaperRealCommonDomainTheorem61Data
alias Theorem6_1_real_commonDomain :=
  PaperRealCommonDomainTheorem61Data.result_every_unitarilyInvariantNorm_across
alias RealCommonDomainTheorem6_2Data :=
  PaperRealCommonDomainTheorem62Data
alias Theorem6_2_real_commonDomain :=
  PaperRealCommonDomainTheorem62Data.result_across
alias Theorem6_2_real_commonDomain_boundNorm_of_finiteRank :=
  PaperRealCommonDomainTheorem62Data.operatorNorm_result_of_rank_le

/-! ## Graph-core appendix forms -/

alias IsGraphCore := ClosedOperator.IsGraphCore
alias CommonCoreResidualData := PaperCommonCoreResidualData
alias commonCoreResidual_extends_to_domain :=
  PaperCommonCoreResidualData.extends_to_domain
alias CommonCoreTheorem6_1Data := PaperCommonCoreTheorem61Data
alias Theorem6_1_commonCore :=
  PaperCommonCoreTheorem61Data.result_every_unitarilyInvariantNorm_across
alias CommonCoreTheorem6_2Data := PaperCommonCoreTheorem62Data
alias Theorem6_2_commonCore := PaperCommonCoreTheorem62Data.result_across
alias RealCommonCoreTheorem6_1Data := PaperRealCommonCoreTheorem61Data
alias Theorem6_1_real_commonCore :=
  PaperRealCommonCoreTheorem61Data.result_every_unitarilyInvariantNorm_across
alias RealCommonCoreTheorem6_2Data := PaperRealCommonCoreTheorem62Data
alias Theorem6_2_real_commonCore :=
  PaperRealCommonCoreTheorem62Data.result_across

/-! ## Sharpness and necessity -/

alias Theorem6_1_equality_every_norm :=
  paperTheorem61_planar_equality_every_norm
alias sineTheta_constant_one_optimal := paperSinTheta_constant_one_optimal
alias oneGap_counterexample_sine_squareNorm :=
  paperCounterexample_sine_square_norm
alias oneGap_counterexample_perturbation_squareNorm :=
  paperCounterexample_perturbation_square_norm
alias oneGap_does_not_imply_Proposition6_1 :=
  paperOneGap_does_not_imply_symmetric_square_estimate

end DavisKahan1970
end TauCeti