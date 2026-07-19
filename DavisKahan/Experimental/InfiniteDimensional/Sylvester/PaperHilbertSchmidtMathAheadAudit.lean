/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperUnitaryInvariantNormInstances
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.PaperHilbertSchmidtDefectFirst
import Spectra.QuantumMechanics.BornRule.Joint.ProjectivePVM

/-!
# Audit surface for the paper norm witness and defect-first square theorem

This module is intentionally excluded from ordinary aggregates.  Compile it
directly after repairing the new infrastructure, then inspect the trusted
assumptions of the listed declarations.
-/

namespace ForMathlib
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
#check closedSylvester_solution_unique_complex
#check paperHilbertSchmidt_sylvester_defectFirst

#print axioms paperUnitaryInvariantNorm_nonempty
#print axioms isPaperHilbertSchmidt_iff_existsUnique_tensor
#print axioms paperHilbertSchmidtNorm_toOperator
#print axioms Spectra.HilbertSchmidtTensor.toOperator_hasGeneratorSylvesterEquation
#print axioms Spectra.QuantumMechanics.SpectralTheory.generator_spectralGapSolution
#print axioms closedSylvester_solution_unique_complex
#print axioms paperHilbertSchmidt_sylvester_defectFirst

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
