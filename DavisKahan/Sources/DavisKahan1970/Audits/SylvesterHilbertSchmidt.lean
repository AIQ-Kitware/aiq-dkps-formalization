/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import DavisKahan.Sources.DavisKahan1970.Ideals.UnitaryInvariantNormInstances
public import DavisKahan.Sources.DavisKahan1970.Sylvester.HilbertSchmidtPairwise

/-!
# Audit surface for the literal square-norm Sylvester theorem

This module is intentionally excluded from ordinary aggregates. Compile it
directly after repairing the new infrastructure, then inspect the trusted
assumptions of every declaration below.

The uniqueness argument uses Tau Ceti's domain-aware Rosenblum theorem and
the native equivalence between the homogeneous Sylvester equation and intertwining.
-/

public section

open TauCeti.DavisKahan.Sylvester

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

#check nuclearNormingFunction
#check symmetricNormingFunction_nonempty
#check HilbertBasis.columnOperator
#check approximationNumberEnergy_ne_top_iff_existsUnique_tensor
#check hilbertSchmidtNorm_toOperator
#check TauCeti.HilbertSchmidt.sylvesterGroup
#check TauCeti.HilbertSchmidt.generator_sylvesterGroup_apply
#check TauCeti.Semigroups.StronglyContinuousGroup.isSelfAdjoint_stoneGenerator
#check TauCeti.LinearPMap.stoneGenerator_genToGroup
#check TauCeti.HilbertSchmidt.isSelfAdjoint_generator_sylvesterGroup
#check IsSelfAdjoint.mem_graph_spectralGapInverse
#check _root_.LinearPMap.Intertwines.eq_zero_of_disjoint_spectrum
#check closedSylvester_homogeneous_eq_zero_of_pairwiseSpectrumGap
#check TauCeti.HilbertSchmidt.hasVectorSpectralGap_sylvesterGroup
#check hilbertSchmidtTensor_hasVectorSpectralGap
#check hilbertSchmidt_sylvester_defectFirst
#check hilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap_direct
#check hilbertSchmidt_sylvester_real_le_of_pairwiseSpectrumGap_direct

#print axioms symmetricNormingFunction_nonempty
#print axioms approximationNumberEnergy_ne_top_iff_existsUnique_tensor
#print axioms hilbertSchmidtNorm_toOperator
#print axioms TauCeti.HilbertSchmidt.generator_sylvesterGroup_apply
#print axioms TauCeti.Semigroups.StronglyContinuousGroup.isSelfAdjoint_stoneGenerator
#print axioms TauCeti.LinearPMap.stoneGenerator_genToGroup
#print axioms TauCeti.HilbertSchmidt.isSelfAdjoint_generator_sylvesterGroup
#print axioms IsSelfAdjoint.mem_graph_spectralGapInverse
#print axioms _root_.LinearPMap.Intertwines.eq_zero_of_disjoint_spectrum
#print axioms closedSylvester_homogeneous_eq_zero_of_pairwiseSpectrumGap
#print axioms TauCeti.HilbertSchmidt.hasVectorSpectralGap_sylvesterGroup
#print axioms hilbertSchmidtTensor_hasVectorSpectralGap
#print axioms hilbertSchmidt_sylvester_defectFirst
#print axioms hilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap_direct
#print axioms hilbertSchmidt_sylvester_real_le_of_pairwiseSpectrumGap_direct

end ExactSinTheta
end DavisKahan
end TauCeti
