/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sources.DavisKahan1970.Ideals.UnitaryInvariantNormInstances
import DavisKahan.Sources.DavisKahan1970.Sylvester.HilbertSchmidtPairwise
import Spectra.QuantumMechanics.BornRule.Joint.ProjectivePVM

/-!
# Audit surface for the literal square-norm Sylvester theorem

This module is intentionally excluded from ordinary aggregates. Compile it
directly after repairing the new infrastructure, then inspect the trusted
assumptions of every declaration below.

Updated 2026-07-29: the uniqueness half of the chain no longer runs through
Spectra's generator-intertwiner, so auditing
`generatorIntertwiner_eq_zero_of_disjoint_spectrum`,
`spectralProjection_intertwines_of_generator` and `GeneratorIntertwines.group`
was auditing constants the theorem no longer depends on.  They are replaced by
the single native endpoint
`TauCeti.LinearPMap.eq_zero_of_intertwines_of_disjoint_spectrum`.  The remaining
`Spectra.HilbertSchmidtTensor.*` entries are SR-D's, and are still load-bearing.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

#check paperNuclearNorm
#check paperUnitaryInvariantNorm_nonempty
#check Spectra.HilbertSchmidtTensor.toOperator
#check isPaperHilbertSchmidt_iff_existsUnique_tensor
#check paperHilbertSchmidtNorm_toOperator
#check Spectra.HilbertSchmidtTensor.sylvesterGroup
#check Spectra.HilbertSchmidtTensor.toOperator_hasGeneratorSylvesterEquation
#check Spectra.QuantumMechanics.SpectralTheory.generator_spectralGapSolution
#check TauCeti.LinearPMap.eq_zero_of_intertwines_of_disjoint_spectrum
#check closedSylvester_homogeneous_eq_zero_of_pairwiseSpectrumGap
#check Spectra.HilbertSchmidtTensor.borelMeasure_sylvesterGroup_tmul
#check Spectra.HilbertSchmidtTensor.spectralProjection_gap_eq_zero
#check paperHilbertSchmidtTensor_hasVectorSpectralGap
#check paperHilbertSchmidt_sylvester_defectFirst
#check paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap_direct
#check paperHilbertSchmidt_sylvester_real_le_of_pairwiseSpectrumGap_direct

#print axioms paperUnitaryInvariantNorm_nonempty
#print axioms isPaperHilbertSchmidt_iff_existsUnique_tensor
#print axioms paperHilbertSchmidtNorm_toOperator
#print axioms Spectra.HilbertSchmidtTensor.toOperator_hasGeneratorSylvesterEquation
#print axioms Spectra.QuantumMechanics.SpectralTheory.generator_spectralGapSolution
#print axioms TauCeti.LinearPMap.eq_zero_of_intertwines_of_disjoint_spectrum
#print axioms closedSylvester_homogeneous_eq_zero_of_pairwiseSpectrumGap
#print axioms Spectra.HilbertSchmidtTensor.borelMeasure_sylvesterGroup_tmul
#print axioms Spectra.HilbertSchmidtTensor.spectralProjection_gap_eq_zero
#print axioms paperHilbertSchmidtTensor_hasVectorSpectralGap
#print axioms paperHilbertSchmidt_sylvester_defectFirst
#print axioms paperHilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap_direct
#print axioms paperHilbertSchmidt_sylvester_real_le_of_pairwiseSpectrumGap_direct

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti